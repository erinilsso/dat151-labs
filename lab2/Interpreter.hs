module Interpreter where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM
import Data.Maybe

type Env = (DefMap, [Context])
type DefMap = Map Id Def
type Context = Map Id (Maybe Val)
data Val =
    VInt Integer 
    | VDouble Double
    | VBool Bool
    | VVoid
    deriving (Eq, Show)

interpret :: Program -> IO ()
interpret (PDefs defs) = do
    env <- foldM updateFun emptyEnv defs
    execProg env

execProg :: Env -> IO ()
execProg env = do
    DFun _ _ _ stms <- lookupFun env (Id "main")
    execStms env stms
    return ()

execStms :: Env -> [Stm] -> IO (Maybe Val, Env)
execStms env (stm:stms) = do
    (retVal, env') <- execStm env stm
    if isJust retVal 
        then return (retVal, env')
        else execStms env' stms
execStms env [] = return (Nothing, env)

execStm :: Env -> Stm -> IO (Maybe Val, Env)
execStm env@(defMap, con:contexts) stm = case stm of
    SExp exp -> do
        (_, env') <- eval env exp
        return (Nothing, env')
    SDecls _ ids -> return (Nothing, foldl declareVar env ids)
    SInit _ id exp -> do
        (val, env') <- eval env exp
        return (Nothing, initVar env' id val)
    SReturn exp -> do
        (val, env') <- eval env exp
        return (Just val, env')
    SWhile exp stm' -> do
        (val, env') <- eval env exp
        if val == VBool True
            then do
                (retVal, env'') <- execStm (newBlock env') stm'
                let retEnv = exitBlock env''
                if isJust retVal
                    then return (retVal, retEnv)
                    else execStm retEnv stm
            else return (Nothing, env')
    SBlock stms -> do
        (retVal, env') <- execStms (newBlock env) stms
        return (retVal, exitBlock env')
    SIfElse exp stm1 stm2 -> do
        (val, env') <- eval env exp
        let evalStm = if val == VBool True
            then stm1
            else stm2
        (retVal, env'') <- execStm (newBlock env') evalStm
        return (retVal, exitBlock env'')
                
evalExps :: Env -> [Exp] -> IO ([Val], Env)
evalExps env (exp:exps) = do
    (val, env') <- eval env exp
    (vals, env'') <- evalExps env' exps
    return (val:vals, env'')
evalExps env [] = return ([], env)

eval :: Env -> Exp -> IO (Val, Env)
eval env@(defMap, contexts) exp = case exp of
    ETrue -> return (VBool True, env)
    EFalse -> return (VBool False, env)
    EInt i -> return (VInt i, env)
    EDouble d -> return (VDouble d, env)
    EId id -> do
        val <- lookupVar env id
        return (val, env)
    EApp id argExps -> do
        (argVals, env') <- evalExps env argExps
        if isBuiltin id
            then do
                val <- evalBuiltin id argVals
                return (val, env')
            else do
                DFun _ _ args stms <- lookupFun env id
                let argIds = [id | (ADecl _ id) <- args]
                let funEnv = foldl (uncurry . initVar) (defMap, [Map.empty]) $ zip argIds argVals
                (retVal, _) <- execStms funEnv stms
                case retVal of
                    Nothing -> return (VVoid, env')
                    Just val -> return (val, env')
    EPostIncr id -> evalIncrDecr env id valPlus True
    EPostDecr id -> evalIncrDecr env id valMinus True
    EPreIncr id -> evalIncrDecr env id valPlus False
    EPreDecr id -> evalIncrDecr env id valMinus False
    ETimes exp1 exp2 -> evalOp env exp1 exp2 valTimes
    EDiv exp1 exp2 -> evalOp env exp1 exp2 valDiv
    EPlus exp1 exp2 -> evalOp env exp1 exp2 valPlus
    EMinus exp1 exp2 -> evalOp env exp1 exp2 valMinus
    ELt exp1 exp2 -> evalOp env exp1 exp2 valLt
    EGt exp1 exp2 -> evalOp env exp1 exp2 valGt
    ELtEq exp1 exp2 -> evalOp env exp1 exp2 valLtEq
    EGtEq exp1 exp2 -> evalOp env exp1 exp2 valGtEq
    EEq exp1 exp2 -> evalOp env exp1 exp2 valEq
    ENEq exp1 exp2 -> evalOp env exp1 exp2 valNEq
    EAnd exp1 exp2 -> do
        (val, env') <- eval env exp1
        case val of
            VBool True -> eval env' exp2
            VBool False -> return (VBool False, env')
    EOr exp1 exp2 -> do
        (val, env') <- eval env exp1
        case val of
            VBool True -> return (VBool True, env')
            VBool False -> eval env' exp2
    EAss id exp -> do
        (val, env') <- eval env exp
        env'' <- updateVar env' id val
        return (val, env'')
    where 
        evalIncrDecr :: Env -> Id -> (Val -> Val -> Val) -> Bool -> IO (Val, Env)
        evalIncrDecr env id op post = do
            val <- lookupVar env id
            let val' = val `op` VInt 1
            env' <- updateVar env id val'
            let retVal = if post then val else val'
            return (retVal, env')
        evalOp :: Env -> Exp -> Exp -> (Val -> Val -> Val) -> IO (Val, Env)
        evalOp env exp1 exp2 op = do
            (val1, env') <- eval env exp1
            (val2, env'') <- eval env' exp2
            let compVal = val1 `op` val2
            return (compVal, env'')

isBuiltin :: Id -> Bool
isBuiltin (Id id) = id `elem` ["printInt", "printDouble", "readInt", "readDouble"]

evalBuiltin :: Id -> [Val] -> IO Val
evalBuiltin (Id "printInt") (VInt i:_) = do
                print i
                return VVoid
evalBuiltin (Id "printDouble") (VDouble d:_) = do
    print d
    return VVoid
evalBuiltin (Id "readInt") _ = VInt <$> readLn
evalBuiltin (Id "readDouble") _ = VDouble <$> readLn

lookupVar :: Env -> Id -> IO Val
lookupVar (defMap, con:contexts) id = case Map.lookup id con of
    Just (Just val) -> return val
    Just Nothing -> fail $ "Uninitialized variable " ++ printTree id
    Nothing -> lookupVar (defMap, contexts) id
lookupVar (_, []) id = fail $ "Undeclared variable " ++ printTree id

lookupFun :: Env -> Id -> IO Def
lookupFun (defMap, _) id = case Map.lookup id defMap of
    Just def -> return def
    Nothing -> fail $ "No function defined with id " ++ printTree id

declareVar :: Env -> Id -> Env
declareVar (defMap, con:contexts) id = (defMap, con':contexts)
    where con' = Map.insert id Nothing con

initVar :: Env -> Id -> Val -> Env
initVar (defMap, con:contexts) id val = (defMap, con':contexts)
    where con' = Map.insert id (Just val) con

updateVar :: Env -> Id -> Val -> IO Env
updateVar (defMap, con:contexts) id val =
    if Map.member id con
    then return (defMap, Map.insert id (Just val) con : contexts)
    else do
        (defMap', contexts') <- updateVar (defMap, contexts) id val
        return (defMap', con:contexts')
updateVar _ id _ = fail $ "No variable declared with id " ++ printTree id 

updateFun :: Env -> Def -> IO Env
updateFun (defMap, contexts) def@(DFun _ id _ _) =
    if Map.member id defMap
    then fail $ "Function name already defined, " ++ printTree id
    else return (Map.insert id def defMap, contexts)

newBlock :: Env -> Env
newBlock (defMap, contexts) = (defMap, Map.empty:contexts)

exitBlock :: Env -> Env
exitBlock (defMap, con:contexts) = (defMap, contexts)

emptyEnv :: Env
emptyEnv = (Map.empty, [Map.empty])

valPlus :: Val -> Val -> Val
valPlus (VInt i) (VInt j) = VInt $ i + j
valPlus (VDouble i) (VDouble j) = VDouble $ i + j
valPlus (VDouble i) (VInt j) = VDouble $ i + fromIntegral j

valMinus :: Val -> Val -> Val
valMinus (VInt i) (VInt j) = VInt $ i - j
valMinus (VDouble i) (VDouble j) = VDouble $ i - j
valMinus (VDouble i) (VInt j) = VDouble $ i - fromIntegral j

valTimes :: Val -> Val -> Val
valTimes (VInt i) (VInt j) = VInt $ i * j
valTimes (VDouble i) (VDouble j) = VDouble $ i * j

valDiv :: Val -> Val -> Val
valDiv (VInt i) (VInt j) = VInt $ i `div` j
valDiv (VDouble i) (VDouble j) = VDouble $ i / j

valLt :: Val -> Val -> Val
valLt (VInt i) (VInt j) = VBool $ i < j
valLt (VDouble i) (VDouble j) = VBool $ i < j

valGt :: Val -> Val -> Val
valGt (VInt i) (VInt j) = VBool $ i > j
valGt (VDouble i) (VDouble j) = VBool $ i > j

valLtEq :: Val -> Val -> Val
valLtEq (VInt i) (VInt j) = VBool $ i <= j
valLtEq (VDouble i) (VDouble j) = VBool $ i <= j

valGtEq :: Val -> Val -> Val
valGtEq (VInt i) (VInt j) = VBool $ i >= j
valGtEq (VDouble i) (VDouble j) = VBool $ i >= j

valEq :: Val -> Val -> Val
valEq (VInt i) (VInt j) = VBool $ i == j
valEq (VDouble i) (VDouble j) = VBool $ i == j
valEq (VBool i) (VBool j) = VBool $ i == j

valNEq :: Val -> Val -> Val
valNEq (VInt i) (VInt j) = VBool $ i /= j
valNEq (VDouble i) (VDouble j) = VBool $ i /= j
valNEq (VBool i) (VBool j) = VBool $ i /= j
