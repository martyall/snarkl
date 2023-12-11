{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use gets" #-}
{-# HLINT ignore "Use camelCase" #-}

module IR
  ( Exp (..),
    toCoreExpr,
    exp_binop,
    exp_seq,
  )
where

import Common (Op, UnOp, Var, is_assoc)
import Control.Monad.Error.Class (throwError)
import Control.Monad.State (State, get, modify, runState)
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Expr as Core
import Field (Field)

data Exp :: Type -> Type where
  EVar :: Var -> Exp a
  EVal :: (Field a) => a -> Exp a
  EUnop :: UnOp -> Exp a -> Exp a
  EBinop :: Op -> [Exp a] -> Exp a
  EIf :: Exp a -> Exp a -> Exp a -> Exp a
  EAssert :: Exp a -> Exp a -> Exp a
  ESeq :: Exp a -> Exp a -> Exp a
  EUnit :: Exp a
  EAbs :: Var -> Exp a -> Exp a
  EApp :: Exp a -> Exp a -> Exp a

deriving instance (Show a) => Show (Exp a)

deriving instance (Eq a) => Eq (Exp a)

type Env a = Map Var (Exp a)

defaultEnv :: Env a
defaultEnv = Map.empty

applyLambdas ::
  (Show a) =>
  Exp a ->
  (Exp a, Env a)
applyLambdas expression = runState (go expression) defaultEnv
  where
    go :: (Show a) => Exp a -> State (Env a) (Exp a)
    go = \case
      EVar var -> do
        ma <- Map.lookup var <$> get
        case ma of
          Nothing -> do
            pure (EVar var)
          Just e -> go e
      e@(EVal _) -> pure e
      EUnit -> pure EUnit
      EUnop op e -> EUnop op <$> go e
      EBinop op es -> EBinop op <$> mapM go es
      EIf b e1 e2 -> EIf <$> go b <*> go e1 <*> go e2
      EAssert (EVar v1) e@(EAbs _ _) -> do
        _e <- go e
        modify $ Map.insert v1 _e
        pure EUnit
      EAssert e1 e2 -> EAssert <$> go e1 <*> go e2
      ESeq e1 e2 -> ESeq <$> go e1 <*> go e2
      -- ESeq :: TExp 'TUnit a -> TExp ty2 a -> TExp ty2 a
      -- EBot :: (Typeable ty) => TExp ty a
      EAbs var e -> do
        EAbs var <$> go e
      EApp (EAbs var e1) e2 -> do
        _e2 <- go e2
        modify $ Map.insert var e2
        go (substitute var e2 e1)
      EApp e1 e2 -> do
        _e1 <- go e1
        _e2 <- go e2
        go (EApp _e1 _e2)

substitute :: (Show a) => Var -> Exp a -> Exp a -> Exp a
substitute var e1 = \case
  e@(EVar var') -> if var == var' then e1 else e
  e@(EVal _) -> e
  EUnit -> EUnit
  EUnop op e -> EUnop op (substitute var e1 e)
  EBinop op es -> EBinop op (map (substitute var e1) es)
  EIf b e2 e3 -> EIf (substitute var e1 b) (substitute var e1 e2) (substitute var e1 e3)
  EAssert e2 e3 -> EAssert (substitute var e1 e2) (substitute var e1 e3)
  ESeq e2 e3 -> ESeq (substitute var e1 e2) (substitute var e1 e3)
  EAbs var' e -> EAbs var' (substitute var e1 e)
  EApp e2 e3 -> EApp (substitute var e1 e2) (substitute var e1 e3)

exp_binop :: Op -> Exp a -> Exp a -> Exp a
exp_binop op e1 e2 =
  case (e1, e2) of
    (EBinop op1 l1, EBinop op2 l2)
      | op1 == op2 && op2 == op && is_assoc op ->
          EBinop op (l1 ++ l2)
    (EBinop op1 l1, _)
      | op1 == op && is_assoc op ->
          EBinop op (l1 ++ [e2])
    (_, EBinop op2 l2)
      | op2 == op && is_assoc op ->
          EBinop op (e1 : l2)
    (_, _) -> EBinop op [e1, e2]

-- | Smart constructor for sequence, ensuring all expressions are
--  flattened to top level.
exp_seq :: Core.Exp a -> Core.Exp a -> Core.Exp a
exp_seq e1 e2 =
  case (e1, e2) of
    (Core.ESeq l1, Core.ESeq l2) -> Core.ESeq (l1 ++ l2)
    (Core.ESeq l1, _) -> Core.ESeq (l1 ++ [e2])
    (_, Core.ESeq l2) -> Core.ESeq (e1 : l2)
    (_, _) -> Core.ESeq [e1, e2]

toCoreExpr :: (Show a) => Exp a -> Core.Exp a
toCoreExpr _exp =
  let (coreExp, _) = applyLambdas _exp
   in case toCoreExpr' coreExp of
        Left err -> error err
        Right e -> e

toCoreExpr' :: (Show a) => Exp a -> Either String (Core.Exp a)
toCoreExpr' = \case
  EVar var -> pure $ Core.EVar var
  EVal v -> pure $ Core.EVal v
  EUnit -> pure Core.EUnit
  EUnop op e -> Core.EUnop op <$> toCoreExpr' e
  EBinop op es -> Core.EBinop op <$> mapM toCoreExpr' es
  EIf b e1 e2 -> Core.EIf <$> toCoreExpr' b <*> toCoreExpr' e1 <*> toCoreExpr' e2
  EAssert e1 e2 -> Core.EAssert <$> toCoreExpr' e1 <*> toCoreExpr' e2
  ESeq e1 e2 -> exp_seq <$> toCoreExpr' e1 <*> toCoreExpr' e2
  e -> throwError ("Impossible after IR simplicifaction: " <> show e)