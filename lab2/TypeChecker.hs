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
isOk Ok _ = True
isOk Bad _ = False

isNumeric :: Type -> Bool
isNumeric Type_int = True
isNumeric Type_double = True
isNumeric _ = False

typecheck :: Program -> Err ()
typecheck p = return ()

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env x expectedType = do
    inferredType <- inferExp env x
    unless (expectedType == inferredType)
        $ fail ("Type of " ++ printTree x
            ++ ". Expected " ++ printTree expectedType
            ++ ", got " ++ printTree inferredType)

checkStms :: Env -> [Stm] -> Err ()
checkStms env stm:stms = 
checkStms _ [] = return ()

checkDef :: Env -> Def -> Err ()
checkDef

checkProgram :: Program -> Err ()
checkProgram

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
            && all isOk . zipWith (checkExp env) args argTypes
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
        inferredType <- infer env x
        if varType == inferredType
            then return varType
            else fail $ "Error in " ++ printTree x 
            ++ ". Tried to assign " ++ printTree inferredType " to " 
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
                inferredType <- inferExp env x1
                if inferredType `elem` allowedTypes
                    then checkExp env x2 inferredType 
                    else fail $  "Error in " ++ printTree x 
                    ++ ". Can't apply operation " ++ op 
                    ++ " to type " ++ printTree inferredType
                    

lookupVar :: Env -> Id -> Err Type
lookupVar (sig, con:contexts ) id = case lookup id con of
    Just varType -> Ok varType
    Nothing -> lookupVar (sig, contexts) id
lookupVar (_, []) id = Bad "No variable defined with id " ++ id

lookupFun :: Env -> Id -> Err ([Type], Type)
lookupFun (sig, _) id = case lookup id sig of
    Just fSig -> Ok fSig
    Nothing -> Bad "No function defined with id " ++ id

updateVar :: Env -> Id -> Type -> Err Env
updateVar (sig, con:contexts) id varType = if member id con
    then fail $ "Variable already defined in context, " ++ id
    else return (sig, insert id varType con : contexts)

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (sig, contexts) id newSig = if member id sig
    then fail $ "Function name already defined, " ++ id
    else return (insert id newSig sig, contexts)

newBlock :: Env -> Env
newBlock (sig, contexts) = (sig, empty:contexts)

emptyEnv :: Env
emptyEnv = (empty, [])