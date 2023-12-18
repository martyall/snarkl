{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# HLINT ignore "Use uncurry" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Test.UnionFindSpec where

import Snarkl.Errors
import Snarkl.UnionFind
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec = do
  describe "UnionFind Algorithm" $ do
    it "finds the root of a single element correctly" $
      property $
        \x -> root (unite empty x x :: UnionFind Int Int) x `shouldBe` (x, unite empty x x)

    it "unifies two elements correctly" $
      property $
        forAll (arbitrary `suchThat` \(x, y) -> x < y) $ \(x, y) ->
          let uf :: UnionFind Int Int
              uf = unite empty x y
              rx = fst $ root uf x
              ry = fst $ root uf y
           in rx `shouldBe` ry

    it "unifies 3 elements correctly" $
      property $
        forAll (arbitrary `suchThat` \(x, y, z) -> x < y && y < z) $ \(x, y, z) ->
          let uf :: UnionFind Int String
              uf = insert z "X" (insert y "X" (insert x "X" empty))
              uf' = unite uf x y
           in do
                fst (root uf' x) `shouldBe` x
                fst (root uf' y) `shouldBe` x
                fst (root uf' z) `shouldBe` z
                let uf'' = unite uf' y z
                fst (root uf'' z) `shouldBe` x
