module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (DefMap, [Context])
type DefMap = Map Id FunSig
type Context = Map Id Type
type FunSig = ([Type], Type)

isOk :: Err a -> Bool
isOk (Ok _) = True
isOk (Bad _) = False

isNumeric :: Type -> Bool
isNumeric Type_int = True
isNumeric Type_double = True
isNumeric _ = False

builtinFuns :: [(Id, FunSig)]
builtinFuns = [
        (Id "printInt", ([Type_int], Type_void)),
        (Id "printDouble", ([Type_double], Type_void)),
        (Id "readInt", ([], Type_int)),
        (Id "readDouble", ([], Type_double))
    ]    

typecheck :: Program -> Err ()
typecheck (PDefs defs) = 
    if mainDef `notElem` userDefFuns
    then fail "No main function with correct signature defined"
    else do
        env <- foldM updateFun' emptyEnv builtinFuns
        env' <- foldM updateFun' env userDefFuns
        mapM_ (checkDef env') defs
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
    SExp exp -> do
        inferExp env exp
        return env
    SDecls varType (id:ids) -> 
        if varType == Type_void
        then fail $ "Error in " ++ printTree stm ++ ". Tried to create a variable of type void."
        else do
            env' <- updateVar env id varType
            checkStm returnType env' $ SDecls varType ids
    SDecls _ [] -> return env
    SInit varType id exp ->
        if varType == Type_void
        then fail $ "Error in " ++ printTree stm ++ ". Tried to create a variable of type void."
        else do
            checkExp env exp varType
            updateVar env id varType
    SReturn exp -> do
        checkExp env exp returnType
        return env
    SWhile exp stm' -> do
        checkExp env exp Type_bool
        checkStm returnType (newBlock env) stm'
        return env
    SIfElse exp stm1 stm2 -> do
        checkExp env exp Type_bool
        checkStm returnType (newBlock env) stm1
        checkStm returnType (newBlock env) stm2
        return env
    SBlock stms -> do
        checkStms returnType (newBlock env) stms
        return env

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env exp expectedType = do
    inferredType <- inferExp env exp
    unless (expectedType == inferredType)
        $ fail ("Type of " ++ printTree exp
            ++ ". Expected " ++ printTree expectedType
            ++ ", got " ++ printTree inferredType)

inferExp :: Env -> Exp -> Err Type
inferExp env exp = case exp of
    ETrue -> return Type_bool
    EFalse -> return Type_bool
    EInt _ -> return Type_int
    EDouble _ -> return Type_double
    EId id -> lookupVar env id
    EApp id args -> do
        (argTypes, retType) <- lookupFun env id
        if length argTypes == length args
            then do
                mapM_ (uncurry $ checkExp env) $ zip args argTypes
                return retType
            else fail $ "Wrong number of arguments in function call " 
                        ++ printTree exp
    EPostIncr id -> inferIncrDecr id
    EPostDecr id -> inferIncrDecr id
    EPreIncr id -> inferIncrDecr id
    EPreDecr id -> inferIncrDecr id
    ETimes exp1 exp2 -> inferNumericOp exp1 exp2 "multiplication"
    EDiv exp1 exp2 -> inferNumericOp exp1 exp2 "division"
    EPlus exp1 exp2 -> inferNumericOp exp1 exp2 "addition"
    EMinus exp1 exp2 -> inferNumericOp exp1 exp2 "subtraction"
    ELt exp1 exp2 -> inferComp exp1 exp2 "less than"
    EGt exp1 exp2 -> inferComp exp1 exp2 "greater than"
    ELtEq exp1 exp2 -> inferComp exp1 exp2 "less than or equal"
    EGtEq exp1 exp2 -> inferComp exp1 exp2 "greater than or equal"
    EEq exp1 exp2 -> inferEq exp1 exp2 "equality"
    ENEq exp1 exp2 -> inferEq exp1 exp2 "inequality"
    EAnd exp1 exp2 -> inferJunc exp1 exp2 "conjunction"
    EOr exp1 exp2 -> inferJunc exp1 exp2 "disjunction"
    EAss id exp -> do
        varType <- lookupVar env id
        inferredType <- inferExp env exp
        if varType == inferredType
        then return varType
        else fail $ "Error in " ++ printTree exp 
            ++ ". Tried to assign " ++ printTree inferredType ++ " to " 
            ++ printTree varType
    where
        inferIncrDecr id' = do
            varType <- lookupVar env id'
            if isNumeric varType
            then return varType
            else fail $ "Error in " ++ printTree exp 
                ++ ". Tried to increment/decrement " ++ printTree varType
        inferNumericOp = inferOp [Type_int, Type_double]
        inferComp = inferCompOp [Type_int, Type_double]
        inferEq = inferCompOp [Type_int, Type_double, Type_bool]
        inferJunc = inferOp [Type_bool]
        inferOp allowedTypes exp1' exp2' op = do 
            inferredType <- inferExp env exp1'
            if inferredType `elem` allowedTypes
            then do
                _ <- checkExp env exp2' inferredType 
                return inferredType
            else fail $  "Error in " ++ printTree exp
                ++ ". Can't apply operation " ++ op 
                ++ " to type " ++ printTree inferredType
        inferCompOp allowedTypes exp1' exp2' op = do
            _ <- inferOp allowedTypes exp1' exp2' op
            return Type_bool

lookupVar :: Env -> Id -> Err Type
lookupVar (defMap, con:contexts ) id = case Map.lookup id con of
    Just varType -> Ok varType
    Nothing -> lookupVar (defMap, contexts) id
lookupVar (_, []) id = Bad $ "No variable defined with id " ++ printTree id

lookupFun :: Env -> Id -> Err FunSig
lookupFun (defMap, _) id = case Map.lookup id defMap of
    Just fSig -> Ok fSig
    Nothing -> Bad $ "No function defined with id " ++ printTree id

updateVar :: Env -> Id -> Type -> Err Env
updateVar env@(defMap, con:contexts) id varType =
    if Map.member id con
    then fail $ "Variable " ++ printTree id ++ " (" ++ printTree varType ++ ")"
            ++ " already defined in context \n" ++ Map.showTreeWith (curry show) True True con
    else return (defMap, Map.insert id varType con : contexts)

updateFun :: Env -> Id -> FunSig -> Err Env
updateFun (defMap, contexts) id newSig =
    if Map.member id defMap
    then fail $ "Function name already defined, " ++ printTree id
    else return (Map.insert id newSig defMap, contexts)

newBlock :: Env -> Env
newBlock (defMap, contexts) = (defMap, Map.empty:contexts)

emptyEnv :: Env
emptyEnv = (Map.empty, [Map.empty])
