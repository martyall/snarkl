{-# OPTIONS_GHC -fno-warn-orphans #-}

module Snarkl.Common where

import Control.Lens (Iso', iso)
import qualified Data.Map as Map
import Data.Ratio
import Prettyprinter

newtype Var = Var Int deriving (Eq, Show, Ord, Pretty, Enum)

unVar :: Iso' Var Int
unVar = iso (\(Var x) -> x) Var

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
