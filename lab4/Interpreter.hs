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

-- data Def = DDef Ident [Ident] Exp
type Err = Except String
type Env = (DefMap, Context)
type DefMap = Map Ident Exp
type Context = Map Ident Val
data Val =
    Closure Exp Context
    | Value Exp

-- | Entry point: Program computes a number.

interpret :: Strategy -> Program -> Err Integer
interpret strategy (Prog defs (DMain mainExp)) = do
    result <- eval (Map.empty, Map.empty) mainExp
    case result of
        Closure (EInt i) _ -> return i
        Value (EInt i) -> return i

-- testEval :: (Env, Exp)
-- testEval = (env, exp)
--   where
--     env = (Map.empty, Map.insert (Ident "a") (EInt 5) Map.empty)
--     exp = EVar (Ident "a")

eval :: Env -> Exp -> Err Val
eval env@(defMap, con) exp = case exp of 
  EVar id -> do
    val <- lookupVal env id
    case val of
        Closure exp' context' -> eval (defMap, context') exp'
        Value exp' -> eval (defMap, Map.empty) exp'
  EInt i -> return $ Value (EInt i)
  EApp exp1 exp2 -> do
    (Closure (EAbs id lambdaExp) lambdaCon) <- eval env exp1
    let param = Closure exp2 con
    env' <- update (defMap, lambdaCon) id param
    eval env' lambdaExp
  EAdd exp1 exp2 -> do
    Value (EInt a) <- eval env exp1
    Value (EInt b) <- eval env exp2
    return $ Value (EInt $ a + b)
  ESub exp1 exp2 -> do
    Value (EInt a) <- eval env exp1
    Value (EInt b) <- eval env exp2
    return $ Value (EInt $ a - b)
  ELt exp1 exp2 -> do
    Value (EInt a) <- eval env exp1
    Value (EInt b) <- eval env exp2
    let bool = if a - b < 0 then 1 else 0
    return $ Value (EInt bool)
  EIf exp1 exp2 exp3 -> do
    bool <- eval env exp1 
    case bool of
      Value (EInt 1) -> eval env exp2
      Value (EInt 0) -> eval env exp3
  EAbs _ _ -> return $ Closure exp con

lookupVal :: Env -> Ident -> Err Val
lookupVal env@(defMap, con) id = case Map.lookup id con of
    Just val -> return val
    Nothing -> case Map.lookup id defMap of
      Just exp -> return $ Closure exp con -- TODO Empty or con?

update :: Env -> Ident -> Val -> Err Env
update (defMap, con) id val = return (defMap, Map.insert id val con)
