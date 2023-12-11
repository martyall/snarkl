{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use gets" #-}

module IR
  ( Exp (..),
    toCoreExpr,
    applyLambdas,
    exp_binop,
    exp_seq,
  )
where

import Common (LambdaVar, Op, UnOp, Var, is_assoc)
import Control.Monad.Error.Class (throwError)
import Control.Monad.State (State, evalState, get, modify)
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Expr as Core
import Field (Field)

data Exp :: Type -> Type where
  EVar :: Var -> Exp a
  ELambdaVar :: LambdaVar -> Exp a
  EVal :: (Field a) => a -> Exp a
  EUnop :: UnOp -> Exp a -> Exp a
  EBinop :: Op -> [Exp a] -> Exp a
  EIf :: Exp a -> Exp a -> Exp a -> Exp a
  EAssert :: Exp a -> Exp a -> Exp a
  ESeq :: [Exp a] -> Exp a
  EUnit :: Exp a
  EAbs :: LambdaVar -> Exp a -> Exp a
  EApp :: Exp a -> Exp a -> Exp a

deriving instance (Show a) => Show (Exp a)

type Env a = Map LambdaVar (Exp a)

applyLambdas ::
  Exp a ->
  Exp a
applyLambdas expression = evalState (go expression) Map.empty
  where
    go :: Exp a -> State (Env a) (Exp a)
    go = \case
      e@(EVar _) -> pure e
      ELambdaVar var -> fromMaybe (ELambdaVar var) . Map.lookup var <$> get
      e@(EVal _) -> pure e
      EUnit -> pure EUnit
      EUnop op e -> EUnop op <$> go e
      EBinop op es -> EBinop op <$> mapM go es
      EIf b e1 e2 -> EIf <$> go b <*> go e1 <*> go e2
      EAssert e1 e2 -> EAssert <$> go e1 <*> go e2
      ESeq es -> ESeq <$> mapM go es
      EAbs var e -> EAbs var <$> go e
      EApp (EAbs var e1) e2 -> do
        _e2 <- go e2
        modify (Map.insert var _e2)
        go e1
      EApp e1 e2 -> do
        _e1 <- go e1
        _e2 <- go e2
        go (EApp _e1 _e2)

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
exp_seq :: Exp a -> Exp a -> Exp a
exp_seq e1 e2 =
  case (e1, e2) of
    (ESeq l1, ESeq l2) -> ESeq (l1 ++ l2)
    (ESeq l1, _) -> ESeq (l1 ++ [e2])
    (_, ESeq l2) -> ESeq (e1 : l2)
    (_, _) -> ESeq [e1, e2]

toCoreExpr :: (Show a) => Exp a -> Core.Exp a
toCoreExpr = either error id . toCoreExpr' . applyLambdas

toCoreExpr' :: (Show a) => Exp a -> Either String (Core.Exp a)
toCoreExpr' = \case
  EVar var -> pure $ Core.EVar var
  EVal v -> pure $ Core.EVal v
  EUnit -> pure Core.EUnit
  EUnop op e -> Core.EUnop op <$> toCoreExpr' e
  EBinop op es -> Core.EBinop op <$> mapM toCoreExpr' es
  EIf b e1 e2 -> Core.EIf <$> toCoreExpr' b <*> toCoreExpr' e1 <*> toCoreExpr' e2
  EAssert e1 e2 -> Core.EAssert <$> toCoreExpr' e1 <*> toCoreExpr' e2
  ESeq es -> Core.ESeq <$> mapM toCoreExpr' es
  e -> throwError ("Impossible after IR simplicifaction: " <> show e)

{-

(\x y -> x y) (\x -> x)

aL (EApp (EAbs x (EAbs y (EApp x y))) (Abs z z))

[(x, Abs z z)]
aL (EAbs y (EApp (EAbs z z) y))

[(x, Abs z z)]
EAbs y (aL (EApp (EAbs z z) y)))

[(x, Abs z z), (z, y)]
EAbs y (aL z y)
EAbs y y

-}

{-
Does this terminate? Need to worry about

(1) Will this always terminate?
(2) Does it always make "progress"?
(3) Do I need to run it multiple times

1) tree never grows, leaves = {EVar, EVal, EUnit} obviously terminate.
2) progress is defined by eliminating any lambdas in position

-}