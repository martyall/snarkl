{-# LANGUAGE GADTs #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Use guards" #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Interp
  ( interp,
    interp_expr,
  )
where

import Common
import Control.Monad
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Errors
import Expr
import Field
import TExpr

type Env a = IntMap (Maybe a)

newtype InterpM a b = InterpM {runInterpM :: Env a -> Either ErrMsg (Env a, b)}

instance Monad (InterpM a) where
  (>>=) mf mg =
    InterpM
      ( \rho -> case runInterpM mf rho of
          Left err -> Left err
          Right (rho', b) -> runInterpM (mg b) rho'
      )
  return b =
    InterpM (\rho -> Right (rho, b))

instance Functor (InterpM a) where
  fmap f mg = return f `ap` mg

instance Applicative (InterpM a) where
  pure = return
  mf <*> ma = ap mf ma

raise_err :: ErrMsg -> InterpM a b
raise_err err =
  InterpM (\_ -> Left err)

add_binds :: [(IntMap.Key, Maybe a1)] -> InterpM a1 (Maybe a2)
add_binds binds =
  InterpM (\rho -> Right (IntMap.union (IntMap.fromList binds) rho, Nothing))

lookup_var :: (Show a) => IntMap.Key -> InterpM a (Maybe a)
lookup_var x =
  InterpM
    ( \rho -> case IntMap.lookup x rho of
        Nothing ->
          Left $
            ErrMsg $
              "unbound var "
                ++ show x
                ++ " in environment "
                ++ show rho
        Just v -> Right (rho, v)
    )

field_of_bool :: (Field a) => Bool -> a
field_of_bool b = if b then one else zero

case_of_field :: (Field a) => Maybe a -> (Maybe Bool -> InterpM a b) -> InterpM a b
case_of_field Nothing f = f Nothing
case_of_field (Just v) f =
  if v == zero
    then f $ Just False
    else
      if v == one
        then f $ Just True
        else raise_err $ ErrMsg $ "expected " ++ show v ++ " to be boolean"

bool_of_field :: (Field a) => a -> InterpM a Bool
bool_of_field v =
  case_of_field
    (Just v)
    ( \mb -> case mb of
        Nothing -> raise_err $ ErrMsg "internal error in bool_of_field"
        Just b -> return b
    )

interp_texp ::
  ( Eq a,
    Show a,
    Field a
  ) =>
  TExp ty1 a ->
  InterpM a (Maybe a)
interp_texp e = do
  let _exp = exp_of_texp e
  interp_expr _exp

interp :: (Field a) => IntMap a -> TExp ty1 a -> Either ErrMsg (Env a, Maybe a)
interp rho e = runInterpM (interp_texp e) $ IntMap.map Just rho

interp_expr ::
  (Field a) =>
  Exp a ->
  InterpM a (Maybe a)
interp_expr e = case e of
  EVar x -> lookup_var x
  EVal v -> pure $ Just v
  EUnop op e2 -> do
    v2 <- interp_expr e2
    case v2 of
      Nothing -> pure Nothing
      Just v2' -> case op of
        ZEq -> return $ Just $ field_of_bool (v2' == zero)
  EBinop op _es -> case _es of
    [] -> fail_with $ ErrMsg $ "empty binary args"
    (a : as) -> do
      b <- interp_expr a
      foldM (interp_binop_expr op) b as
  EIf eb e1 e2 ->
    do
      mb <- interp_expr eb
      case mb of
        Nothing -> pure Nothing
        Just _b -> bool_of_field _b >>= \b -> if b then interp_expr e1 else interp_expr e2
  EAssert e1 e2 ->
    case (e1, e2) of
      (EVar x, _) ->
        do
          v2 <- interp_expr e2
          add_binds [(x, v2)]
      (_, _) -> raise_err $ ErrMsg $ show e1 ++ " not a variable"
  ESeq es -> last <$> mapM interp_expr es
  EUnit -> return $ Just one
  where
    interp_binop_expr :: (Field a) => Op -> Maybe a -> Exp a -> InterpM a (Maybe a)
    interp_binop_expr _ Nothing _ = return Nothing
    interp_binop_expr _op (Just a1) _exp = do
      ma2 <- interp_expr _exp
      case ma2 of
        Nothing -> return Nothing
        Just a2 -> Just <$> op a1 a2
      where
        op :: (Field a) => a -> a -> InterpM a a
        op a b = case _op of
          Add -> pure $ a `add` b
          Sub -> pure $ a `add` neg b
          Mult -> pure $ a `mult` b
          Div -> pure $
            case inv b of
              Nothing -> fail_with $ ErrMsg $ show b ++ " not invertible"
              Just b' -> a `mult` b'
          And -> interp_boolean_binop a b
          Or -> interp_boolean_binop a b
          XOr -> interp_boolean_binop a b
          BEq -> interp_boolean_binop a b
          Eq -> pure $ field_of_bool $ a == b
        interp_boolean_binop :: (Field a) => a -> a -> InterpM a a
        interp_boolean_binop a b =
          do
            b1 <- bool_of_field a
            b2 <- bool_of_field b
            case _op of
              And -> return $ field_of_bool $ b1 && b2
              Or -> return $ field_of_bool $ b1 || b2
              XOr -> return $ field_of_bool $ (b1 && not b2) || (b2 && not b1)
              BEq -> return $ field_of_bool $ b1 == b2
              _ -> fail_with $ ErrMsg "internal error in interp_binop"