module Snarkl.Backend.R1CS.Poly where

import Data.Field.Galois (PrimeField)
import qualified Data.IntMap.Lazy as Map
import Snarkl.Common

data Poly a where
  Poly :: (PrimeField a) => Assgn a -> Poly a

instance (Show a) => Show (Poly a) where
  show (Poly m) = show m

-- | The constant polynomial equal 'c'
const_poly :: (PrimeField a) => a -> Poly a
const_poly c = Poly $ Map.insert (-1) c Map.empty

-- | The polynomial equal variable 'x'
var_poly ::
  (PrimeField a) =>
  -- | Variable, with coeff
  (a, Var) ->
  -- | Resulting polynomial
  Poly a
var_poly (coeff, x) =
  Poly $ Map.insert x coeff Map.empty
