{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module TExpr
  ( Val (..),
    TExp (..),
    TFunct (..),
    Ty (..),
    Rep,
    TUnop (..),
    TOp (..),
    TVar (..),
    Loc,
    TLoc (..),
    TLambdaVar (..),
    boolean_vars_of_texp,
    var_of_texp,
    loc_of_texp,
    te_seq,
    last_seq,
    exp_of_texp,
    ir_of_texp,
  )
where

import Common
import Data.Typeable
import Errors
import Expr
import Field
import qualified IR

data TFunct where
  TFConst :: Ty -> TFunct
  TFId :: TFunct
  TFProd :: TFunct -> TFunct -> TFunct
  TFSum :: TFunct -> TFunct -> TFunct
  TFComp :: TFunct -> TFunct -> TFunct
  deriving (Typeable)

data Ty where
  TField :: Ty
  TBool :: Ty
  TArr :: Ty -> Ty
  TProd :: Ty -> Ty -> Ty
  TSum :: Ty -> Ty -> Ty
  TMu :: TFunct -> Ty
  TUnit :: Ty
  TFun :: Ty -> Ty -> Ty
  deriving (Typeable)

type family Rep (f :: TFunct) (x :: Ty) :: Ty

type instance Rep ('TFConst ty) x = ty

type instance Rep 'TFId x = x

type instance Rep ('TFProd f g) x = 'TProd (Rep f x) (Rep g x)

type instance Rep ('TFSum f g) x = 'TSum (Rep f x) (Rep g x)

type instance Rep ('TFComp f g) x = Rep f (Rep g x)

newtype TVar (ty :: Ty) = TVar Var

var_is_boolean :: (Typeable ty) => TVar ty -> Bool
var_is_boolean x =
  typeOf x == typeOf (undefined :: TVar 'TBool)

instance Eq (TVar ty) where
  TVar x == TVar y = x == y

instance Show (TVar ty) where
  show (TVar x) = show x

newtype TLambdaVar (ty :: Ty) = TLambdaVar LambdaVar

type Loc = Int

newtype TLoc (ty :: Ty) = TLoc Loc

instance Eq (TLoc ty) where
  TLoc x == TLoc y = x == y

instance Show (TLoc ty) where
  show (TLoc x) = "loc_" ++ show x

data TUnop :: Ty -> Ty -> * where
  TUnop :: forall ty1 ty. UnOp -> TUnop ty1 ty
  deriving (Eq)

data TOp :: Ty -> Ty -> Ty -> * where
  TOp :: forall ty1 ty2 ty. Op -> TOp ty1 ty2 ty
  deriving (Eq)

data Val :: Ty -> * -> * where
  VField :: (Field a) => a -> Val 'TField a
  VTrue :: Val 'TBool a
  VFalse :: Val 'TBool a
  VUnit :: Val 'TUnit a
  VLoc :: TLoc ty -> Val ty a

data TExp :: Ty -> * -> * where
  TEVar :: TVar ty -> TExp ty a
  TELambdaVar :: TLambdaVar ty -> TExp ty a
  TEVal :: Val ty a -> TExp ty a
  TEUnop ::
    ( Typeable ty1
    ) =>
    TUnop ty1 ty ->
    TExp ty1 a ->
    TExp ty a
  TEBinop ::
    ( Typeable ty1,
      Typeable ty2
    ) =>
    TOp ty1 ty2 ty ->
    TExp ty1 a ->
    TExp ty2 a ->
    TExp ty a
  TEIf :: TExp 'TBool a -> TExp ty a -> TExp ty a -> TExp ty a
  TEAssert :: (Typeable ty) => TExp ty a -> TExp ty a -> TExp 'TUnit a
  TESeq :: TExp 'TUnit a -> TExp ty2 a -> TExp ty2 a
  TEBot :: (Typeable ty) => TExp ty a
  TEAbs :: (Typeable ty, Typeable ty1) => TLambdaVar ty -> TExp ty1 a -> TExp ('TFun ty ty1) a
  TEApp :: (Typeable ty, Typeable ty1) => TExp ('TFun ty ty1) a -> TExp ty a -> TExp ty1 a

exp_of_val :: (Field a) => Val ty a -> Exp a
exp_of_val v = case v of
  VField c -> EVal c
  VTrue -> EVal one
  VFalse -> EVal zero
  VUnit -> EUnit
  VLoc l -> fail_with $ ErrMsg $ "unresolved location " ++ show l

ir_of_val :: (Field a) => Val ty a -> IR.Exp a
ir_of_val v = case v of
  VField c -> IR.EVal c
  VTrue -> IR.EVal one
  VFalse -> IR.EVal zero
  VUnit -> IR.EUnit
  VLoc l -> fail_with $ ErrMsg $ "unresolved location " ++ show l

ir_of_texp :: (Field a) => TExp ty a -> IR.Exp a
ir_of_texp te = case te of
  TEVar (TVar x) -> IR.EVar x
  TEVal v -> ir_of_val v
  TEUnop (TUnop op) te1 ->
    IR.EUnop op (ir_of_texp te1)
  TEBinop (TOp op) te1 te2 ->
    IR.exp_binop op (ir_of_texp te1) (ir_of_texp te2)
  TEIf te1 te2 te3 ->
    IR.EIf (ir_of_texp te1) (ir_of_texp te2) (ir_of_texp te3)
  TEAssert te1 te2 ->
    IR.EAssert (ir_of_texp te1) (ir_of_texp te2)
  TESeq te1 te2 -> IR.exp_seq (ir_of_texp te1) (ir_of_texp te2)
  TEBot -> IR.EUnit
  TELambdaVar (TLambdaVar v) -> IR.ELambdaVar v
  TEAbs (TLambdaVar v) e -> IR.EAbs v (ir_of_texp e)
  TEApp e1 e2 -> IR.EApp (ir_of_texp e1) (ir_of_texp e2)

instance
  ( Field a,
    Eq a
  ) =>
  Eq (Val ty a)
  where
  v1 == v2 = exp_of_val v1 == exp_of_val v2

exp_of_texp :: (Field a) => TExp ty a -> Exp a
exp_of_texp te =
  IR.toCoreExpr $ IR.applyLambdas $ ir_of_texp te

instance
  ( Field a,
    Eq a
  ) =>
  Eq (TExp ty a)
  where
  te1 == te2 = exp_of_texp te1 == exp_of_texp te2

-- | Smart constructor for 'TESeq'.  Simplify 'TESeq te1 te2' to 'te2'
-- whenever the normal form of 'te1' (with seq's reassociated right)
-- is *not* equal 'TEAssert _ _'.
te_seq :: (Typeable ty1) => TExp ty1 a -> TExp ty2 a -> TExp ty2 a
te_seq te1 te2 = case (te1, te2) of
  (TEAssert _ _, _) -> TESeq te1 te2
  (TESeq tx ty, _) -> te_seq tx (te_seq ty te2)
  (_, _) -> te2

boolean_vars_of_texp :: (Typeable ty) => TExp ty a -> [Var]
boolean_vars_of_texp = go []
  where
    go :: (Typeable ty) => [Var] -> TExp ty a -> [Var]
    go vars (TEVar t@(TVar x)) =
      if var_is_boolean t
        then x : vars
        else vars
    go vars (TEVal _) = vars
    go vars (TEUnop _ e1) = go vars e1
    go vars (TEBinop _ e1 e2) = go (go vars e1) e2
    go vars (TEIf e1 e2 e3) =
      go (go (go vars e1) e2) e3
    go vars (TEAssert e1 e2) = go (go vars e1) e2
    go vars (TESeq e1 e2) = go (go vars e1) e2
    go vars TEBot = vars
    go vars (TELambdaVar _) = vars
    go vars (TEAbs _ e) = go vars e
    go vars (TEApp e1 e2) = go (go vars e1) e2

var_of_texp :: (Show a) => TExp ty a -> Var
var_of_texp te = case last_seq te of
  TEVar (TVar x) -> x
  _ -> fail_with $ ErrMsg ("var_of_texp: expected var: " ++ show te)

loc_of_texp :: (Show a) => TExp ty a -> Var
loc_of_texp te = case last_seq te of
  TEVal (VLoc (TLoc l)) -> l
  _ -> fail_with $ ErrMsg ("loc_of_texp: expected loc: " ++ show te)

last_seq :: TExp ty a -> TExp ty a
last_seq te = case te of
  TESeq _ te2 -> last_seq te2
  _ -> te

instance Show (TUnop ty1 ty) where
  show (TUnop op) = show op

instance Show (TOp ty1 ty2 ty) where
  show (TOp op) = show op

instance (Show a) => Show (Val ty a) where
  show (VField c) = show c
  show VTrue = "true"
  show VFalse = "false"
  show VUnit = "()"
  show (VLoc l) = "loc_" ++ show l

instance (Show a) => Show (TExp ty a) where
  show (TEVar x) = "var " ++ show x
  show (TEVal c) = show c
  show (TEUnop op e1) = show op ++ show e1
  show (TEBinop op e1 e2) = show e1 ++ show op ++ show e2
  show (TEIf b e1 e2) =
    "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (TEAssert e1 e2) = show e1 ++ " := " ++ show e2
  show (TESeq e1 e2) = "(" ++ show e1 ++ "; " ++ show e2 ++ ")"
  show TEBot = "bot"
  show (TELambdaVar (TLambdaVar v)) = show v
  show (TEAbs (TLambdaVar v) e) = "(\\" <> show v <> " -> " <> show e <> ")"
  show (TEApp e1 e2) = "(" <> show e1 <> ") (" <> show e2 <> ")"
