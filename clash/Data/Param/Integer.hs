module Data.Param.Integer
  ( Signed(..)
  , Unsigned(..)
  , Index (..)
  , HWBits(..)
  ) where

import Types
import qualified Data.Bits as B

newtype (NaturalT nT) => Signed nT = Signed Integer

newtype (NaturalT nT) => Unsigned nT = Unsigned Integer

newtype (PositiveT upper) => Index upper = Index Integer

class (B.Bits a) => HWBits a where
  shiftL :: a -> a -> a
  shiftR :: a -> a -> a
