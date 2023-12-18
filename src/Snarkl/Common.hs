{-# OPTIONS_GHC -fno-warn-orphans #-}

module Snarkl.Common
  ( Assgn,
    UnOp (..),
    Op (..),
    isBoolean,
    isAssoc,
    Var,
    mkVar,
    unVar,
    incVar,
    incVarBy,
  )
where

import qualified Data.Map as Map
import Data.Ratio
import Prettyprinter

type Assgn a = Map.Map Var a

data UnOp = ZEq
  deriving (Eq, Show)

instance Pretty UnOp where
  pretty ZEq = "isZero"

data Op
  = Add
  | Sub
  | Mult
  | Div
  | And
  | Or
  | XOr
  | Eq
  | BEq
  deriving (Eq, Show)

instance Pretty Op where
  pretty Add = "+"
  pretty Sub = "-"
  pretty Mult = "*"
  pretty Div = "-*"
  pretty And = "&&"
  pretty Or = "||"
  pretty XOr = "xor"
  pretty Eq = "=="
  pretty BEq = "=b="

isBoolean :: Op -> Bool
isBoolean op = case op of
  Add -> False
  Sub -> False
  Mult -> False
  Div -> False
  And -> True
  Or -> True
  XOr -> True
  Eq -> True
  BEq -> True

isAssoc :: Op -> Bool
isAssoc op = case op of
  Add -> True
  Sub -> False
  Mult -> True
  Div -> False
  And -> True
  Or -> True
  XOr -> True
  Eq -> True
  BEq -> True

instance Pretty Rational where
  pretty r
    | denominator r == 1 = pretty (numerator r)
    | otherwise = pretty (numerator r) <> "/" <> pretty (denominator r)

newtype Var = Var Int deriving (Eq, Ord, Enum, Show, Pretty)

mkVar :: Int -> Var
mkVar = Var

unVar :: Var -> Int
unVar (Var x) = x

incVar :: Var -> Var
incVar (Var x) = Var (x + 1)

incVarBy :: Int -> Var -> Var
incVarBy n (Var x) = Var (x + n)
