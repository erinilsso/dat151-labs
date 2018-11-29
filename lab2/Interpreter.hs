-- EPostIncr id -> do
--     val <- lookupVar env id
--     let val' = case val of
--             VInt i -> VInt $ i + 1
--             VDouble d -> VDouble $ d + 1
--     env' <- updateVar env id val'
--     return (val, env')
-- EPostDecr id -> do
--     val <- lookupVar env id
--     let val' = case val of
--             VInt i -> VInt $ i - 1
--             VDouble d -> VDouble $ d - 1
--     env' <- updateVar env id val'
--     return (val, env')
-- EPreIncr id -> do
--     val <- lookupVar env id
--     let val' = case val of
--             VInt i -> VInt $ i + 1
--             VDouble d -> VDouble $ d + 1
--     env' <- updateVar env id val'
--     return (val', env')
-- EPreDecr id -> do
--     val <- lookupVar env id
--     let val' = case val of
--             VInt i -> VInt $ i - 1
--             VDouble d -> VDouble $ d - 1
--     env' <- updateVar env id val'
--     return (val', env')

module Interpreter where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (DefMap, [Context])
type DefMap = Map Id Def
type Context = Map Id Val
data Val =
    VInt Integer 
    | VDouble Double
    | VBool Bool
    | VVoid
    deriving (Eq, Show)

valPlus :: Val -> Val -> Val
valPlus (VInt i) (VInt j) = VInt $ i + j
valPlus (VDouble i) (VDouble j) = VDouble $ i + j
valPlus (VDouble i) (VInt j) = VDouble $ i + fromIntegral j

valMinus :: Val -> Val -> Val
valMinus (VInt i) (VInt j) = VInt $ i * j
valMinus (VDouble i) (VDouble j) = VDouble $ i - j
valMinus (VDouble i) (VInt j) = VDouble $ i - fromIntegral j

valTimes :: Val -> Val -> Val
valTimes (VInt i) (VInt j) = VInt $ i * j
valTimes (VDouble i) (VDouble j) = VDouble $ i * j

valDiv :: Val -> Val -> Val
valDiv (VInt i) (VInt j) = VInt $ i `div` j
valDiv (VDouble i) (VDouble j) = VDouble $ i / j

interpret :: Program -> IO ()
interpret p = putStrLn "no interpreter yet"

-- execProg :: Env -> Err ()

execFun :: Env -> [Stm] -> Err Val
execFun env (stm:stms) = case stm of
    SReturn exp -> do
        (val, _) <- eval env exp
        return val
    _ -> do
        env' <- execStm env stm
        execFun env' stms
execFun _ [] = return VVoid

execStm :: Env -> Stm -> Err Env
execStm env stm = case stm of
    SWhile exp stm' -> do
        (val, env') <- eval env exp
        if val == VBool True
        then do
            env'' <- execStm env' stm'
            execStm env'' stm
        else return env'

evalExps :: Env -> [Exp] -> Err ([Val], Env)
evalExps env (exp:exps) = do
    (val, env') <- eval env exp
    (vals, env'') <- evalExps env' exps
    return (val:vals, env'')
evalExps env [] = return ([], env)

eval :: Env -> Exp -> Err (Val, Env)
eval env@(defMap, contexts) exp = case exp of
    ETrue -> return (VBool True, env)
    EFalse -> return (VBool True, env)
    EInt i -> return (VInt i, env)
    EDouble d -> return (VDouble d, env)
    EId id -> do
        val <- lookupVar env id
        return (val, env)
    EApp id argExps -> do
        (argVals, env') <- evalExps env argExps
        DFun _ _ args stms <- lookupFun env id
        let argIds = [id | (ADecl _ id) <- args]
        funEnv <- foldM (uncurry . updateVar) (defMap, [Map.empty]) $ zip argIds argVals
        retVal <- execFun funEnv stms
        return (retVal, env')
    EPostIncr id -> evalIncrDecr env id valPlus True
    EPostDecr id -> evalIncrDecr env id valMinus True
    EPreIncr id -> evalIncrDecr env id valPlus False
    EPreDecr id -> evalIncrDecr env id valMinus False
    ETimes exp1 exp2 -> evalNumericOp env exp1 exp2 valTimes
    EDiv exp1 exp2 -> evalNumericOp env exp1 exp2 valDiv
    EPlus exp1 exp2 -> evalNumericOp env exp1 exp2 valPlus
    EMinus exp1 exp2 -> evalNumericOp env exp1 exp2 valMinus
    -- ELt x1 x2 -> inferNumericOp x1 x2 "less than"
    -- EGt x1 x2 -> inferNumericOp x1 x2 "greater than"
    -- ELtEq x1 x2 -> inferNumericOp x1 x2 "less than or equal"
    -- EGtEq x1 x2 -> inferNumericOp x1 x2 "greater than or equal"
    -- EEq x1 x2 -> inferEq x1 x2 "equality"
    -- ENEq x1 x2 -> inferEq x1 x2 "inequality"
    -- EAnd x1 x2 -> inferJunc x1 x2 "conjunction"
    -- EOr x1 x2 -> inferJunc x1 x2 "disjunction"
    -- EAss id x -> do
    --     varType <- lookupVar env id
    --     inferredType <- inferExp env x
    --     if varType == inferredType
    --     then return varType
    --     else fail $ "Error in " ++ printTree x 
    --         ++ ". Tried to assign " ++ printTree inferredType ++ " to " 
    --         ++ printTree varType
    where 
        evalIncrDecr :: Env -> Id -> (Val -> Val -> Val) -> Bool -> Err (Val, Env)
        evalIncrDecr env id op post = do
            val <- lookupVar env id
            let val' = val `op` VInt 1
            env' <- updateVar env id val'
            let retVal = if post then val else val'
            return (retVal, env')
        evalNumericOp :: Env -> Exp -> Exp -> (Val -> Val -> Val) -> Err (Val, Env)
        evalNumericOp env exp1 exp2 op = do
            (val1, env') <- eval env exp1
            (val2, env'') <- eval env' exp2
            let compVal = val1 `op` val2
            return (compVal, env'')

lookupVar :: Env -> Id -> Err Val
lookupVar (defMap, con:contexts) id = case Map.lookup id con of
    Just val -> Ok val
    Nothing -> lookupVar (defMap, contexts) id
lookupVar (_, []) id = Bad $ "No variable defined with id " ++ printTree id

lookupFun :: Env -> Id -> Err Def
lookupFun (defMap, _) id = case Map.lookup id defMap of
    Just def -> Ok def
    Nothing -> Bad $ "No function defined with id " ++ printTree id

updateVar :: Env -> Id -> Val -> Err Env
updateVar (defMap, con:contexts) id val =
    -- Try to update the value of the variable in the existing contexts
    -- If the variable isn't defined, add it to the current context
    case updateVar' (con:contexts) id val of
        Just contexts' -> return (defMap, contexts')
        Nothing -> return (defMap, Map.insert id val con : contexts)

-- Updates the value of the variable in the context it is defined
-- and returns the new list of contexts. If the variable isn't defined,
-- Nothing is returned
updateVar' :: [Context] -> Id -> Val -> Maybe [Context]
updateVar' (con:contexts) id val =
    if Map.member id con
    then return (Map.insert id val con : contexts)
    else do
        contexts' <- updateVar' contexts id val
        return (con:contexts')
updateVar' [] id val = Nothing

updateFun :: Env -> Def -> Err Env
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