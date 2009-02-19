-- | This module provides the HsValueMap type, which can structurally map a
--   Haskell value to something else.
module HsValueMap where

import qualified Type
import qualified TyCon
import Control.Applicative
import Data.Traversable
import Data.Foldable

-- | A datatype that maps each of the single values in a haskell structure to
-- a mapto. The map has the same structure as the haskell type mapped, ie
-- nested tuples etc.
data HsValueMap mapto =
  Tuple [HsValueMap mapto]
  | Single mapto
  deriving (Show, Eq, Ord)

instance Functor HsValueMap where
  fmap f (Single s) = Single (f s)
  fmap f (Tuple maps) = Tuple (map (fmap f) maps)

instance Foldable HsValueMap where
  foldMap f (Single s) = f s
  -- The first foldMap folds a list of HsValueMaps, the second foldMap folds
  -- each of the HsValueMaps in that list
  foldMap f (Tuple maps) = foldMap (foldMap f) maps

instance Traversable HsValueMap where
  traverse f (Single s) = Single <$> f s
  traverse f (Tuple maps) = Tuple <$> (traverse (traverse f) maps)

data PassState s x = PassState (s -> (s, x))

instance Functor (PassState s) where
  fmap f (PassState a) = PassState (\s -> let (s', a') = a s in (s', f a'))

instance Applicative (PassState s) where
  pure x = PassState (\s -> (s, x))
  PassState f <*> PassState x = PassState (\s -> let (s', f') = f s; (s'', x') = x s' in (s'', f' x'))

-- | Creates a HsValueMap with the same structure as the given type, using the
--   given function for mapping the single types.
mkHsValueMap ::
  Type.Type                         -- ^ The type to map to a HsValueMap
  -> HsValueMap Type.Type           -- ^ The resulting map and state

mkHsValueMap ty =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) ->
      if (TyCon.isTupleTyCon tycon) 
        then
          Tuple (map mkHsValueMap args)
        else
          Single ty
    Nothing -> Single ty

-- | Creates a map of pairs from two maps. The maps must have the same
--   structure.
zipValueMaps :: (Show a, Show b) => HsValueMap a -> HsValueMap b -> HsValueMap (a, b)
zipValueMaps = zipValueMapsWith (\a b -> (a, b))

-- | Creates a map of two maps using the given combination function.
zipValueMapsWith :: (Show a, Show b) => (a -> b -> c) -> HsValueMap a -> HsValueMap b -> HsValueMap c
zipValueMapsWith f (Tuple as) (Tuple bs) =
  Tuple $ zipWith (zipValueMapsWith f) as bs
zipValueMapsWith f (Single a) (Single b) =
  Single $ f a b
zipValueMapsWith _ a b =
  --Tuple []
  error $ "Trying to zip unsimilarly formed trees!\n" ++ (show a) ++ "\nand\n" ++ (show b)

