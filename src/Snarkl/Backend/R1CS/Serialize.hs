module Snarkl.Backend.R1CS.Serialize (serialize_r1cs, serialize_assgn) where

import Data.Field.Galois (Prime, PrimeField (fromP))
import qualified Data.IntMap.Lazy as Map
import GHC.TypeLits (KnownNat)
import Snarkl.Backend.R1CS.Poly
import Snarkl.Backend.R1CS.R1CS
import Snarkl.Common

serialize_assgn :: (KnownNat p) => Assgn (Prime p) -> String
serialize_assgn m =
  let binds = Map.toAscList $ Map.mapKeys (+ 1) m
   in concat $
        map (\(_, v) -> show (fromP v) ++ "\n") binds

serialize_poly :: Poly (Prime p) -> String
serialize_poly p = case p of
  Poly m ->
    let size = Map.size m
        binds = Map.toList $ Map.mapKeys (+ 1) m
        string_binds =
          map
            ( \(k, v) ->
                show k
                  ++ "\n"
                  ++ show (fromP v)
                  ++ "\n"
            )
            binds
     in show size
          ++ "\n"
          ++ concat string_binds

serialize_r1c :: R1C (Prime p) -> String
serialize_r1c cons = case cons of
  R1C (a, b, c) -> concat $ map serialize_poly [a, b, c]

serialize_r1cs :: R1CS (Prime p) -> String
serialize_r1cs cs =
  let r1c_strings :: String
      r1c_strings = concat (map serialize_r1c (r1cs_clauses cs))
      num_in_vars = length $ r1cs_in_vars cs
   in show num_in_vars
        ++ "\n"
        ++ show (r1cs_num_vars cs - num_in_vars)
        ++ "\n"
        ++ show (length $ r1cs_clauses cs)
        ++ "\n"
        ++ r1c_strings
