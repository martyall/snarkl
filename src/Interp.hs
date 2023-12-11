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
import Control.Monad.Cont (MonadTrans (lift))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Debug.Trace (traceM)
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
  traceM $ "interp_texp: " ++ show e
  let _exp = exp_of_texp e
  traceM $ "interp_texp: exp: " ++ show _exp
  interp_expr _exp

interp :: (Field a) => IntMap a -> TExp ty1 a -> Either ErrMsg (Env a, Maybe a)
interp rho e = runInterpM (interp_texp e) $ IntMap.map Just rho

interp_expr ::
  (Field a) =>
  Exp a ->
  InterpM a (Maybe a)
interp_expr e = case e of
  EVar x -> do
    traceM $ "interp_expr: EVar " ++ show x
    lookup_var x
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

{-
examples: Impossible after IR simplicifaction:

interp_texp: TESeq (TEAssert (TEVar 3) (TEVar 1)) (TESeq (TEAssert (TEVar 4) (TEVar 2)) (TESeq (TEAssert (TEVar 5) (TEVar 0)) (TESeq (TEAssert (TEVar 7) (TEVar 6)) (TESeq (TEAssert (TEVar 8) (TEVar 7)) (TESeq (TEAssert (TEVar 9) (TEVar 7)) (TESeq (TEAssert (TEVar 10) (TEVar 3)) (TESeq (TEAssert (TEVar 11) (TEVar 3)) (TESeq (TEAssert (TEVar 12) (TEVar 5)) (TESeq (TEAssert (TEVar 13) (TEIf (TEVar 12) (TEVar 10) (TEVar 11))) (TESeq (TEAssert (TEVar 14) (TEVar 7)) (TESeq (TEAssert (TEVar 15) (TEBinop * (TEVar 13) (TEVar 14))) (TESeq (TEAssert (TEVar 16) (TEVar 7)) (TESeq (TEAssert (TEVar 17) (TEBinop * (TEVar 15) (TEVar 16))) (TESeq (TEAssert (TEVar 18) (TEVar 3)) (TESeq (TEAssert (TEVar 19) (TEBinop * (TEVar 17) (TEVar 18))) (TESeq (TEAssert (TEVar 20) (TEVar 3)) (TESeq (TEAssert (TEVar 21) (TEVar 3)) (TESeq (TEAssert (TEVar 22) (TEVar 3)) (TESeq (TEAssert (TEVar 23) (TEVar 4)) (TESeq (TEAssert (TEVar 24) (TEBinop * (TEVar 19) (TEVar 20))) (TESeq (TEAssert (TEVar 25) (TEIf (TEVar 23) (TEVar 21) (TEVar 22))) (TESeq (TEAssert (TEVar 26) (TEBinop * (TEVar 8) (TEVar 9))) (TESeq (TEAssert (TEVar 27) (TEBinop * (TEVar 24) (TEVar 25))) (TESeq (TEAssert (TEVar 28) (TEVar 3)) (TESeq (TEAssert (TEVar 29) (TEVal 2 % 1))

(TESeq
  (TEAssert
    (TEVar 30)
    (TEAbs 6 (TESeq (TEAssert (TEVar 7) (TEVar 6)) (TESeq (TEAssert (TEVar 8) (TEVar 7)) (TESeq (TEAssert (TEVar 9) (TEVar 7)) (TESeq (TEAssert (TEVar 10) (TEVar 3)) (TESeq (TEAssert (TEVar 11) (TEVar 3)) (TESeq (TEAssert (TEVar 12) (TEVar 5)) (TESeq (TEAssert (TEVar 13) (TEIf (TEVar 12) (TEVar 10) (TEVar 11))) (TESeq (TEAssert (TEVar 14) (TEVar 7)) (TESeq (TEAssert (TEVar 15) (TEBinop * (TEVar 13) (TEVar 14))) (TESeq (TEAssert (TEVar 16) (TEVar 7)) (TESeq (TEAssert (TEVar 17) (TEBinop * (TEVar 15) (TEVar 16))) (TESeq (TEAssert (TEVar 18) (TEVar 3)) (TESeq (TEAssert (TEVar 19) (TEBinop * (TEVar 17) (TEVar 18))) (TESeq (TEAssert (TEVar 20) (TEVar 3)) (TESeq (TEAssert (TEVar 21) (TEVar 3)) (TESeq (TEAssert (TEVar 22) (TEVar 3)) (TESeq (TEAssert (TEVar 23) (TEVar 4)) (TESeq (TEAssert (TEVar 24) (TEBinop * (TEVar 19) (TEVar 20))) (TESeq (TEAssert (TEVar 25) (TEIf (TEVar 23) (TEVar 21) (TEVar 22))) (TESeq (TEAssert (TEVar 26) (TEBinop * (TEVar 8) (TEVar 9))) (TESeq (TEAssert (TEVar 27) (TEBinop * (TEVar 24) (TEVar 25))) (TEBinop - (TEVar 26) (TEVar 27)))))))))))))))))))))))))

     (TESeq (TEAssert (TEVar 31) (TEBinop + (TEVar 28) (TEVar 29))) (TEApp (TEVar 30) (TEVar 31))))

interp_texp: TESeq (TEAssert (TEVar 3) (TEVar 1)) (TESeq (TEAssert (TEVar 4) (TEVar 2)) (TESeq (TEAssert (TEVar 5) (TEVar 0)) (TESeq (TEAssert (TEVar 7) (TEVar 6)) (TESeq (TEAssert (TEVar 8) (TEVar 7)) (TESeq (TEAssert (TEVar 9) (TEVar 7)) (TESeq (TEAssert (TEVar 10) (TEVar 3)) (TESeq (TEAssert (TEVar 11) (TEVar 3)) (TESeq (TEAssert (TEVar 12) (TEVar 5)) (TESeq (TEAssert (TEVar 13) (TEIf (TEVar 12) (TEVar 10) (TEVar 11))) (TESeq (TEAssert (TEVar 14) (TEVar 7)) (TESeq (TEAssert (TEVar 15) (TEBinop * (TEVar 13) (TEVar 14))) (TESeq (TEAssert (TEVar 16) (TEVar 7)) (TESeq (TEAssert (TEVar 17) (TEBinop * (TEVar 15) (TEVar 16))) (TESeq (TEAssert (TEVar 18) (TEVar 3)) (TESeq (TEAssert (TEVar 19) (TEBinop * (TEVar 17) (TEVar 18))) (TESeq (TEAssert (TEVar 20) (TEVar 3)) (TESeq (TEAssert (TEVar 21) (TEVar 3)) (TESeq (TEAssert (TEVar 22) (TEVar 3)) (TESeq (TEAssert (TEVar 23) (TEVar 4)) (TESeq (TEAssert (TEVar 24) (TEBinop * (TEVar 19) (TEVar 20))) (TESeq (TEAssert (TEVar 25) (TEIf (TEVar 23) (TEVar 21) (TEVar 22))) (TESeq (TEAssert (TEVar 26) (TEBinop * (TEVar 8) (TEVar 9))) (TESeq (TEAssert (TEVar 27) (TEBinop * (TEVar 24) (TEVar 25))) (TESeq (TEAssert (TEVar 28) (TEVar 3)) (TESeq (TEAssert (TEVar 29) (TEVal 2 % 1)) (TESeq (TEAssert (TEVar 30) (TEAbs 6 (TESeq (TEAssert (TEVar 7) (TEVar 6)) (TESeq (TEAssert (TEVar 8) (TEVar 7)) (TESeq (TEAssert (TEVar 9) (TEVar 7)) (TESeq (TEAssert (TEVar 10) (TEVar 3)) (TESeq (TEAssert (TEVar 11) (TEVar 3)) (TESeq (TEAssert (TEVar 12) (TEVar 5)) (TESeq (TEAssert (TEVar 13) (TEIf (TEVar 12) (TEVar 10) (TEVar 11))) (TESeq (TEAssert (TEVar 14) (TEVar 7)) (TESeq (TEAssert (TEVar 15) (TEBinop * (TEVar 13) (TEVar 14))) (TESeq (TEAssert (TEVar 16) (TEVar 7)) (TESeq (TEAssert (TEVar 17) (TEBinop * (TEVar 15) (TEVar 16))) (TESeq (TEAssert (TEVar 18) (TEVar 3)) (TESeq (TEAssert (TEVar 19) (TEBinop * (TEVar 17) (TEVar 18))) (TESeq (TEAssert (TEVar 20) (TEVar 3)) (TESeq (TEAssert (TEVar 21) (TEVar 3)) (TESeq (TEAssert (TEVar 22) (TEVar 3)) (TESeq (TEAssert (TEVar 23) (TEVar 4)) (TESeq (TEAssert (TEVar 24) (TEBinop * (TEVar 19) (TEVar 20))) (TESeq (TEAssert (TEVar 25) (TEIf (TEVar 23) (TEVar 21) (TEVar 22))) (TESeq (TEAssert (TEVar 26) (TEBinop * (TEVar 8) (TEVar 9))) (TESeq (TEAssert (TEVar 27) (TEBinop * (TEVar 24) (TEVar 25))) (TEBinop - (TEVar 26) (TEVar 27))))))))))))))))))))))))) (TESeq (TEAssert (TEVar 31) (TEBinop + (TEVar 28) (TEVar 29))) (TEApp (TEVar 30) (TEVar 31)))))))))))))))))))))))))))))

interp_texp: exp: (var 3 := var 1; var 4 := var 2; var 5 := var 0; var 7 := var 6; var 8 := var 7; var 9 := var 7; var 10 := var 3; var 11 := var 3; var 12 := var 5; var 13 := if var 12 then var 10 else var 11; var 14 := var 7; var 15 := var 13*var 14; var 16 := var 7; var 17 := var 15*var 16; var 18 := var 3; var 19 := var 17*var 18; var 20 := var 3; var 21 := var 3; var 22 := var 3; var 23 := var 4; var 24 := var 19*var 20; var 25 := if var 23 then var 21 else var 22; var 26 := var 8*var 9; var 27 := var 24*var 25; var 28 := var 3; var 29 := 2 % 1; (); var 31 := var 28+var 29; var 7 := var 31; var 8 := var 7; var 9 := var 7; var 10 := var 3; var 11 := var 3; var 12 := var 5; var 13 := if var 12 then var 10 else var 11; var 14 := var 7; var 15 := var 13*var 14; var 16 := var 7; var 17 := var 15*var 16; var 18 := var 3; var 19 := var 17*var 18; var 20 := var 3; var 21 := var 3; var 22 := var 3; var 23 := var 4; var 24 := var 19*var 20; var 25 := if var 23 then var 21 else var 22; var 26 := var 8*var 9; var 27 := var 24*var 25; var 26-var 27)

TESeq
  (TEAssert (TEVar 3) (TEVar 1))
  (TESeq
    (TEAssert (TEVar 4) (TEVar 2))
    (TESeq
      (TEAssert (TEVar 5) (TEVar 0))
      (TESeq
        (TEAssert (TEVar 28) (TEVar 3))
        (TESeq
          (TEAssert (TEVar 29) (TEVal 2 % 1))
          (TESeq
            (TEAssert (TEVar 30)
            (TEAbs 6 (TEBinop - (TEVar 26) (TEVar 27))))
            (TESeq
              (TEAssert (TEVar 31)
              (TEBinop + (TEVar 28) (TEVar 29)))
              (TEApp (TEVar 30) (TEVar 31))))))))
TEAssert

prog1 :: Snarkl.Comp 'TField
prog1 =
  let prog :: (Bool, (Rational, Bool)) -> Rational
      prog (x, (y, z)) =
        let u = y + 2
            v = if z then y else y
            w = if x then y else y
         in u * u - (w * u * u * y * y * v)

         interp_texp: TESeq (TEAssert (TEVar 3) (TEVar 1)) (TESeq (TEAssert (TEVar 4) (TEVar 2)) (TESeq (TEAssert (TEVar 5) (TEVar 0)) (TESeq (TEAssert (TEVar 28) (TEVar 3)) (TESeq (TEAssert (TEVar 29) (TEVal 2 % 1)) (TESeq (TEAssert (TEVar 30) (TEAbs 6 (TEBinop - (TEVar 26) (TEVar 27)))) (TESeq (TEAssert (TEVar 31) (TEBinop + (TEVar 28) (TEVar 29))) (TEApp (TEVar 30) (TEVar 31))))))))
interp_texp: exp: (var 3 := var 1; var 4 := var 2; var 5 := var 0;

var 28 := var 3;
var 29 := 2 % 1;
var 31 := var 28 + var 29;
var 26 - var 27)

var 3 := var 1;
var 4 := var 2;
var 5 := var 0;

var 7 := var 6; # bad

var 8 := var 7;
var 9 := var 7;

var 10 := var 3;
var 11 := var 3;

var 12 := var 5;

var 13 := if var 12 then var 10 else var 11;

var 14 := var 7;

var 15 := var 13 * var 14;

var 16 := var 7;

var 17 := var 15 * var 16;

var 18 := var 3;

var 19 := var 17 * var 18;

var 20 := var 3;
var 21 := var 3;
var 22 := var 3;

var 23 := var 4;

var 24 := var 19 * var 20;

var 25 := if var 23 then var 21 else var 22;

var 26 := var 8*var 9;

var 27 := var 24*var 25;

var 28 := var 3;

var 29 := 2 % 1;

var 31 := var 28 + var 29;

var 7 := var 31;

var 8 := var 7;
var 9 := var 7;

var 10 := var 3;
var 11 := var 3;

var 12 := var 5;

var 13 := if var 12 then var 10 else var 11;

var 14 := var 7;

var 15 := var 13*var 14;

var 16 := var 7;

var 17 := var 15*var 16;

var 18 := var 3;

var 19 := var 17*var 18;

var 20 := var 3;
var 21 := var 3;
var 22 := var 3;

var 23 := var 4;

var 24 := var 19*var 20;

var 25 := if var 23 then var 21 else var 22;

var 26 := var 8*var 9;

var 27 := var 24*var 25;

var 26-var 27)

-}