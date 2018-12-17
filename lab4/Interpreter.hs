-- | Interpreter for lambda-calculus with if, +, -, <.
--
--   Strategy can be either call-by-value or call-by-name.

{-# LANGUAGE LambdaCase #-}

module Interpreter (interpret, Strategy(..)) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map

import Fun.Abs
import Fun.Print

-- | Evaluation strategy.

data Strategy
  = CallByName
  | CallByValue

-- | Error monad.

type Err = Except String
type Env = (DefMap, Context)
type DefMap = Map Ident Exp
type Context = Map Ident Val
data Val =
    Closure Exp Context
    | Value Exp
    deriving (Show)

-- | Entry point: Program computes a number.

interpret :: Strategy -> Program -> Err Integer
interpret strategy (Prog defs (DMain mainExp)) = do
  let env = (foldl insertDef Map.empty defs, Map.empty)
  eval strategy env mainExp >>= toInt "expression in main"
  where
    insertDef :: DefMap -> Def -> DefMap
    insertDef map def@(DDef id _ _) = Map.insert id (convertDef def) map
    convertDef :: Def -> Exp    
    convertDef (DDef id (argId:argIds) exp) = EAbs argId (convertDef $ DDef id argIds exp)
    convertDef (DDef _ [] exp) = exp
  
eval :: Strategy -> Env -> Exp -> Err Val
eval strategy env@(defMap, con) exp = case exp of 
  EVar id -> do
    val <- lookupVal env id
    case val of
        Closure exp' context' -> eval strategy (defMap, context') exp'
        Value exp' -> eval strategy (defMap, Map.empty) exp'
  EInt i -> return $ Value (EInt i)
  EApp exp1 exp2 -> do
    res <- eval strategy env exp1
    case res of
      (Closure (EAbs id lambdaExp) lambdaCon) -> do
        param <- case strategy of
          CallByValue -> eval strategy env exp2
          CallByName -> return $ Closure exp2 con
        env' <- update (defMap, lambdaCon) id param
        eval strategy env' lambdaExp
      _ -> fail $ "INTERPRETER ERROR: " ++ show res ++ " is not a function"
  EAdd exp1 exp2 -> do
    a <- eval strategy env exp1 >>= toInt exp1
    b <- eval strategy env exp2 >>= toInt exp2
    return $ Value (EInt $ a + b)
  ESub exp1 exp2 -> do
    a <- eval strategy env exp1 >>= toInt exp1
    b <- eval strategy env exp2 >>= toInt exp2
    return $ Value (EInt $ a - b)
  ELt exp1 exp2 -> do
    a <- eval strategy env exp1 >>= toInt exp1
    b <- eval strategy env exp2 >>= toInt exp2
    let bool = if a - b < 0 then 1 else 0
    return $ Value (EInt bool)
  EIf exp1 exp2 exp3 -> do
    bool <- eval strategy env exp1 >>= toInt exp1
    case bool of
      1 -> eval strategy env exp2
      0 -> eval strategy env exp3
      _ -> fail $ "INTERPRETER ERROR: expected " ++ show exp1 
                  ++ " to be 0 or 1, got " ++ show bool
  EAbs _ _ -> return $ Closure exp con

toInt :: Show a => a -> Val -> Err Integer
toInt _ (Value (EInt a)) = return a
toInt output _ = fail $ "INTERPRETER ERROR: " ++ show output ++ " is not an int"

lookupVal :: Env -> Ident -> Err Val
lookupVal env@(defMap, con) id =
  case Map.lookup id con of
    Just val -> return val
    Nothing -> case Map.lookup id defMap of
      Just exp -> return $ Value exp
      Nothing -> fail $ "INTERPRETER ERROR: Nothing called " ++ show id ++ " defined"

update :: Env -> Ident -> Val -> Err Env
update (defMap, con) id val = return (defMap, Map.insert id val con)
