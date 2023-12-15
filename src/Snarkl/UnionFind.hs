module Snarkl.UnionFind
  ( root,
    unite,
    new_uf,
    extra_of,
    UnionFind (..),
  )
where

import Control.Lens ((^.))
import qualified Data.IntMap.Lazy as IntMap
import Data.Maybe
import Snarkl.Common
import Snarkl.Errors

data UnionFind a = UnionFind
  { ids :: IntMap.IntMap Var,
    sizes :: IntMap.IntMap Int,
    extras :: IntMap.IntMap a
  }
  deriving (Show)

new_uf :: UnionFind a
new_uf = UnionFind IntMap.empty IntMap.empty IntMap.empty

id_of :: UnionFind a -> Var -> Var
id_of uf x = fromMaybe x $ IntMap.lookup (x ^. _Var) (ids uf)

size_of :: UnionFind a -> Var -> Int
size_of uf x = fromMaybe 1 $ IntMap.lookup (x ^. _Var) (sizes uf)

extra_of :: UnionFind a -> Var -> Maybe a
extra_of uf x = IntMap.lookup (x ^. _Var) (extras uf)

root :: (Show a, Eq a) => UnionFind a -> Var -> (Var, UnionFind a)
root uf x =
  let px = id_of uf x
   in if px == x
        then (x, uf)
        else
          let gpx = id_of uf px
              uf' = merge_extras uf x gpx
           in root (uf' {ids = IntMap.insert (x ^. _Var) gpx (ids uf)}) px

merge_extras :: (Show a, Eq a) => UnionFind a -> Var -> Var -> UnionFind a
merge_extras uf x y =
  case (IntMap.lookup (x ^. _Var) (extras uf), IntMap.lookup (y ^. _Var) (extras uf)) of
    (Nothing, Nothing) -> uf
    (Nothing, Just d) -> uf {extras = IntMap.insert (x ^. _Var) d (extras uf)}
    (Just c, Nothing) -> uf {extras = IntMap.insert (y ^. _Var) c (extras uf)}
    (Just c, Just d) ->
      if c == d
        then uf
        else
          failWith $
            ErrMsg
              ( "in UnionFind, extra data doesn't match:\n  "
                  ++ show (x, c)
                  ++ " != "
                  ++ show (y, d)
              )

-- | Unify x with y.  On ties, prefer smaller variables. This is just
-- a heuristic that biases toward pinned variables, many of which are
-- low-numbered input vars. This way, we avoid introducing pinned
-- eqns. in some cases.
unite :: (Show a, Eq a) => UnionFind a -> Var -> Var -> UnionFind a
unite uf x y
  | x < y =
      go x y
  | x > y =
      go y x
  | otherwise =
      uf
  where
    -- Left-biased: if size x == size y, prefer x as root.
    go x0 y0 =
      let (rx, uf2) = root uf x0
          (ry, uf') = root uf2 y0
          sz_rx = size_of uf' rx
          sz_ry = size_of uf' ry
       in if sz_rx >= sz_ry
            then
              uf'
                { ids = IntMap.insert (y0 ^. _Var) rx (ids uf'),
                  sizes = IntMap.insert (x0 ^. _Var) (sz_rx + sz_ry) (sizes uf')
                }
            else
              uf'
                { ids = IntMap.insert (x0 ^. _Var) ry (ids uf'),
                  sizes = IntMap.insert (y0 ^. _Var) (sz_rx + sz_ry) (sizes uf')
                }
