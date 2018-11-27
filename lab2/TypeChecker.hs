module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (Sig, [Context])
type Sig = Map Id ([Type], Type)
type Context = Map Id Type

isOk :: Err a -> Bool
isOk (Ok _) = True
isOk (Bad _) = False

isNumeric :: Type -> Bool
isNumeric Type_int = True
isNumeric Type_double = True
isNumeric _ = False

builtinFuns :: [(Id, ([Type], Type))]
builtinFuns = [
        (Id "printInt", ([Type_int], Type_void)),
        (Id "printDouble", ([Type_double], Type_void)),
        (Id "readInt", ([], Type_int)),
        (Id "readDouble", ([], Type_double))
    ]    

typecheck :: Program -> Err ()
typecheck (PDefs defs) = 
    if mainDef `notElem` userDefFuns
    -- TODO: Print what is wrong with main instead of a generic error
    then fail "No main function with correct signature defined"
    else do
        env <- foldM updateFun' emptyEnv builtinFuns
        env' <- foldM updateFun' env userDefFuns
        foldM_ checkDef env' defs
    where
        mainDef = (Id "main", ([], Type_int))
        updateFun' env = uncurry (updateFun env)
        userDefFuns = [
            (id, ([varType | (ADecl varType argId) <- args], retType)) 
            | (DFun retType id args _) <- defs ]

checkDef :: Env -> Def -> Err Env
checkDef env (DFun returnType id args stms) = do
    (env', argTypes) <- checkArgs env args
    checkStms returnType env' stms

checkArgs :: Env -> [Arg] -> Err (Env, [Type])
checkArgs env = foldM checkArg (env, [])

checkArg :: (Env, [Type]) -> Arg -> Err (Env, [Type])
checkArg (env, types) arg@(ADecl varType id) =
    if varType == Type_void
    then fail $ "Error in " ++ printTree arg ++ ". Tried to create a variable of type void."
    else do
        env' <- updateVar env id varType
        return (env', varType:types)        

checkStms :: Type -> Env -> [Stm] -> Err Env
checkStms returnType = foldM (checkStm returnType)

checkStm :: Type -> Env -> Stm -> Err Env
checkStm returnType env stm = case stm of
    SExp x -> do
        inferExp env x
        return env
    SDecls varType (id:ids) -> 
        if varType == Type_void
        then fail $ "Error in " ++ printTree stm ++ ". Tried to create a variable of type void."
        else do
            env' <- updateVar env id varType
            checkStm returnType env' $ SDecls varType ids
    SDecls _ [] -> return env
    SInit varType id x ->
        if varType == Type_void
        then fail $ "Error in " ++ printTree stm ++ ". Tried to create a variable of type void."
        else do
            checkExp env x varType
            updateVar env id varType
    SReturn x -> do
        checkExp env x returnType
        return env
    SWhile x stm' -> do
        checkExp env x Type_bool
        checkStm returnType env stm'
        return env
    SIfElse x stm1 stm2 -> do
        checkExp env x Type_bool
        checkStm returnType env stm1
        checkStm returnType env stm2
        return env
    SBlock stms -> do
        checkStms returnType (newBlock env) stms
        return env

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env x expectedType = do
    inferredType <- inferExp env x
    unless (expectedType == inferredType)
        $ fail ("Type of " ++ printTree x
            ++ ". Expected " ++ printTree expectedType
            ++ ", got " ++ printTree inferredType)

inferExp :: Env -> Exp -> Err Type
inferExp env x = case x of
    ETrue -> return Type_bool
    EFalse -> return Type_bool
    EInt _ -> return Type_int
    EDouble _ -> return Type_double
    EId id -> lookupVar env id
    EApp id args -> do
        (argTypes, retType) <- lookupFun env id
        -- TODO: Don't swallow errors for checkExp for args
        if length argTypes == length args
            && all isOk (zipWith (checkExp env) args argTypes)
        then return retType
        else fail $ "Type error in argument for function call " ++ printTree x
    EPostIncr id -> inferIncrDecr id
    EPostDecr id -> inferIncrDecr id
    EPreIncr id -> inferIncrDecr id
    EPreDecr id -> inferIncrDecr id
    ETimes x1 x2 -> inferNumericOp x1 x2 "multiplication"
    EDiv x1 x2 -> inferNumericOp x1 x2 "division"
    EPlus x1 x2 -> inferNumericOp x1 x2 "addition"
    EMinus x1 x2 -> inferNumericOp x1 x2 "subtraction"
    ELt x1 x2 -> inferNumericOp x1 x2 "less than"
    EGt x1 x2 -> inferNumericOp x1 x2 "greater than"
    ELtEq x1 x2 -> inferNumericOp x1 x2 "less than or equal"
    EGtEq x1 x2 -> inferNumericOp x1 x2 "greater than or equal"
    EEq x1 x2 -> inferEq x1 x2 "equality"
    ENEq x1 x2 -> inferEq x1 x2 "inequality"
    EAnd x1 x2 -> inferJunc x1 x2 "conjunction"
    EOr x1 x2 -> inferJunc x1 x2 "disjunction"
    EAss id x -> do
        varType <- lookupVar env id
        inferredType <- inferExp env x
        if varType == inferredType
        then return varType
        else fail $ "Error in " ++ printTree x 
            ++ ". Tried to assign " ++ printTree inferredType ++ " to " 
            ++ printTree varType
    where
        inferIncrDecr id' = do
            varType <- lookupVar env id'
            if isNumeric varType
            then return varType
            else fail $ "Error in " ++ printTree x 
                ++ ". Tried to increment/decrement " ++ printTree varType
        inferNumericOp = inferOp [Type_int, Type_double]
        inferEq = inferOp [Type_int, Type_double, Type_bool]
        inferJunc = inferOp [Type_bool]
        inferOp allowedTypes x1' x2' op = do 
            inferredType <- inferExp env x1'
            if inferredType `elem` allowedTypes
            then do
                _ <- checkExp env x2' inferredType 
                return inferredType
            else fail $  "Error in " ++ printTree x
                ++ ". Can't apply operation " ++ op 
                ++ " to type " ++ printTree inferredType

lookupVar :: Env -> Id -> Err Type
lookupVar (sig, con:contexts ) id = case Map.lookup id con of
    Just varType -> Ok varType
    Nothing -> lookupVar (sig, contexts) id
lookupVar (_, []) id = Bad $ "No variable defined with id " ++ printTree id

lookupFun :: Env -> Id -> Err ([Type], Type)
lookupFun (sig, _) id = case Map.lookup id sig of
    Just fSig -> Ok fSig
    Nothing -> Bad $ "No function defined with id " ++ printTree id

updateVar :: Env -> Id -> Type -> Err Env
updateVar (sig, con:contexts) id varType =
    if Map.member id con
    then fail $ "Variable already defined in context, " ++ printTree id
    else return (sig, Map.insert id varType con : contexts)

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (sig, contexts) id newSig =
    if Map.member id sig
    then fail $ "Function name already defined, " ++ printTree id
    else return (Map.insert id newSig sig, contexts)

newBlock :: Env -> Env
newBlock (sig, contexts) = (sig, Map.empty:contexts)

emptyEnv :: Env
emptyEnv = (Map.empty, [Map.empty])
