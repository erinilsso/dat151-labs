-- Optional: turn on warnings.
-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

-- | Compiler for C--, producing symbolic JVM assembler.

module Compiler where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import CPP.Abs

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

data Env = Env {
  vars :: [Map Id Int],
  stackPtr :: Int,
  code :: [Instruction],
  labelCount :: Int,
  funs :: Map Id JVMFunType,
  className :: String
} deriving (Show)

type Instruction = String
type JVMFunType = String
type Label = String

-- | Entry point.

compile
  :: String  -- ^ Class name.
  -> Program -- ^ Type-annotated program.
  -> String  -- ^ Generated jasmin source file content.
compile name (PDefs defs) = header ++ concatMap compile' defs
  where
    funEnv :: Env
    funEnv = foldl extendFun (emptyEnv name) defs
    compile' :: Def -> String
    compile' def = unlines . reverse . code $ execState (compileDef def) funEnv        
    header :: String
    header = unlines
      [ ";; BEGIN HEADER"
      , ""
      , ".class public " ++ name
      , ".super java/lang/Object"
      , ""
      , ".method public <init>()V"
      , "  .limit locals 1"
      , ""
      , "  aload_0"
      , "  invokespecial java/lang/Object/<init>()V"
      , "  return"
      , ""
      , ".end method"
      , ""
      , ".method public static main([Ljava/lang/String;)V"
      , "  .limit locals 1"
      , "  .limit stack  1"
      , ""
      , "  invokestatic " ++ name ++ "/main()I"
      , "  pop"
      , "  return"
      , ""
      , ".end method"
      , ""
      , ";; END HEADER"
      , ""
      ]

compileDef :: Def -> State Env ()
compileDef (DFun retType id args stms) = do
  jvmFunType <- lookupFun id
  emitMeta $ ".method public static " ++ jvmFunType
  emitMeta ".limit locals 1000"
  emitMeta ".limit stack 1000"
  mapM_ storeArg args
  mapM_ compileStm stms
  when (retType == Type_void) $ emit "return"
  emitMeta ".end method"
  emit ""
  where
    storeArg (ADecl _ id) = extendVar id

compileStm :: Stm -> State Env ()
compileStm stm = case stm of
  SExp exp -> do
    compileExp exp
    noPop <- isVoidFunApp exp
    unless noPop $ emit "pop"
  SDecls _ ids -> mapM_ extendVar ids
  SInit _ id exp -> do
    compileExp exp
    addr <- extendVar id
    emit $ "istore " ++ show addr
  SReturn exp ->  do
    compileExp exp
    emit "ireturn"
  SWhile exp stm' -> do
    testLabel <- newLabel "TEST"
    endLabel <- newLabel "END"
    emitLabel testLabel
    compileExp exp
    emit $ "ifeq " ++ endLabel
    newBlock
    compileStm stm'
    exitBlock
    emit $ "goto " ++ testLabel
    emitLabel endLabel
  SIfElse exp stm1 stm2 -> do
    falseLabel <- newLabel "FALSE"
    trueLabel <- newLabel "TRUE"
    compileExp exp
    newBlock
    emit $ "ifeq " ++ falseLabel
    compileStm stm1
    emit $ "goto " ++ trueLabel
    emitLabel falseLabel
    compileStm stm2
    emitLabel trueLabel
    emit "nop"
    exitBlock
  SBlock stms -> do
    newBlock
    mapM_ compileStm stms
    exitBlock
  where
    isVoidFunApp :: Exp -> State Env Bool
    isVoidFunApp (EApp id _) = isVoidFun id
    isVoidFunApp _ = return False

    isVoidFun :: Id -> State Env Bool
    isVoidFun id = do
      jvmFunType <- lookupFun id
      return $ last jvmFunType == 'V'

compileExp :: Exp -> State Env ()
compileExp exp = case exp of
  ETrue -> emit "bipush 1"
  EFalse -> emit "bipush 0"
  EInt i -> emit $ "ldc " ++ show i
  EId id -> lookupVar id >>= (\x -> emit $ "iload " ++ show x)
  EApp id args -> do
    mapM_ compileExp args
    jvmSig <- getJvmSig id
    emit $ "invokestatic " ++ jvmSig
  EPostIncr id -> do
    addr <- lookupVar id
    emit $ "iload " ++ show addr
    emit $ "iinc " ++ show addr ++ " 1"
  EPostDecr id -> do
    addr <- lookupVar id
    emit $ "iload " ++ show addr
    emit $ "iinc " ++ show addr ++ " -1"
  EPreIncr id -> do
    addr <- lookupVar id
    emit $ "iinc " ++ show addr ++ " 1"
    emit $ "iload " ++ show addr
  EPreDecr id -> do
    addr <- lookupVar id
    emit $ "iinc " ++ show addr ++ " -1"
    emit $ "iload " ++ show addr
  ETimes exp1 exp2 -> compileNumericOp exp1 exp2 "imul"
  EDiv exp1 exp2 -> compileNumericOp exp1 exp2 "idiv"
  EPlus exp1 exp2 -> compileNumericOp exp1 exp2 "iadd"
  EMinus exp1 exp2 -> compileNumericOp exp1 exp2 "isub"
  ELt exp1 exp2 -> compileCompOp exp1 exp2 "if_icmplt"
  EGt exp1 exp2 -> compileCompOp exp1 exp2 "if_icmpgt"
  ELtEq exp1 exp2 -> compileCompOp exp1 exp2 "if_icmple"
  EGtEq exp1 exp2 -> compileCompOp exp1 exp2 "if_icmpge"
  EEq exp1 exp2 -> compileCompOp exp1 exp2 "if_icmpeq"
  ENEq exp1 exp2 -> compileCompOp exp1 exp2 "if_icmpne"
  EAnd exp1 exp2 -> compileJuncOp exp1 exp2 "ifeq"
  EOr exp1 exp2 -> compileJuncOp exp1 exp2 "ifne"
  EAss id exp -> do
      compileExp exp
      addr <- lookupVar id
      emit "dup"
      emit $ "istore " ++ show addr
  where
    compileNumericOp exp1 exp2 op = do
      compileExp exp1 
      compileExp exp2
      emit op

    compileCompOp exp1 exp2 op = do
      compileExp exp1
      compileExp exp2
      trueLabel <- newLabel "TRUE"
      endLabel <- newLabel "END"
      emit $ op ++ " " ++ trueLabel
      emit "bipush 0"
      emit $ "goto " ++ endLabel
      emitLabel trueLabel
      emit "bipush 1"
      emitLabel endLabel

    compileJuncOp exp1 exp2 op = do
      compileExp exp1
      endLabel <- newLabel "END"
      emit "dup"
      emit $ op ++ " " ++ endLabel
      emit "pop"
      compileExp exp2 
      emitLabel endLabel

emit :: Instruction -> State Env ()
emit i = emit' $ "  " ++ i

emitMeta :: String -> State Env ()
emitMeta = emit'

emitLabel :: Label -> State Env ()
emitLabel l = emit' $ l ++ ":"

emit' :: String -> State Env ()
emit' str = modify (\env -> env{code = str : code env})

lookupVar :: Id -> State Env Int
lookupVar id = gets $ lookupVar' . vars
  where lookupVar' (con:cons) = fromMaybe (lookupVar' cons) (Map.lookup id con)

lookupFun :: Id -> State Env JVMFunType
lookupFun (Id "printInt") = return "printInt(I)V"
lookupFun (Id "printDouble") = return "printDouble(D)V"
lookupFun (Id "readInt") = return "readInt()I"
lookupFun (Id "readDouble") = return "readDouble()D"
lookupFun id = gets $ fromJust . Map.lookup id . funs

getJvmSig :: Id -> State Env JVMFunType
getJvmSig id = do
  env <- get
  let className' = if isBuiltin id
      then "Runtime"
      else className env
  jvmFunType <- lookupFun id
  return $ className' ++ "/" ++ jvmFunType
  where
    isBuiltin :: Id -> Bool
    isBuiltin (Id name) = name `elem` ["printInt", "printDouble", "readInt", "readDouble"]

extendVar :: Id -> State Env Int
extendVar id = do
  env <- get
  let stackPos = stackPtr env
  let (varMap:vars') = vars env
  modify (\env -> env{
    vars = Map.insert id stackPos varMap : vars',
    stackPtr = stackPos + 1
  })
  return stackPos

extendFun :: Env -> Def -> Env
extendFun env def@(DFun _ id _ _) = env{funs = Map.insert id (translate def) (funs env)}
  where
    translate :: Def -> JVMFunType
    translate (DFun retType (Id name) args _) = name 
            ++ "(" ++ map translateArg args ++ ")" 
            ++ [getJVMType retType]
    
    translateArg :: Arg -> Char
    translateArg (ADecl varType _) = getJVMType varType

    getJVMType :: Type -> Char
    getJVMType Type_bool = 'Z'
    getJVMType Type_int = 'I'
    getJVMType Type_void = 'V'
    

newBlock :: State Env ()
newBlock = modify (\env -> env{vars = Map.empty:vars env})

exitBlock :: State Env ()
exitBlock = do
  env <- get
  let (currCon:cons) = vars env
  let stackPtr' = stackPtr env - Map.size currCon   
  modify (\env -> env{
    vars = cons,
    stackPtr = stackPtr'
    })

emptyEnv :: String -> Env
emptyEnv className = Env{
  vars = [Map.empty],
  stackPtr = 0,
  code = [],
  labelCount = 0,
  funs = Map.empty,
  className = className
}

newLabel :: String -> State Env Label
newLabel prefix = do
  env <- get
  modify (\env -> env{labelCount = 1 + labelCount env})
  return $ prefix ++ show (labelCount env)

testCompileExp :: Exp -> IO ()
testCompileExp exp = putStrLn . List.intercalate "\n" . reverse . code $ execState (compileExp exp) (emptyEnv "Foo")
