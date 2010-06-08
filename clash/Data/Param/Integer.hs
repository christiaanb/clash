module Data.Param.Integer
  ( Signed(..)
  , Unsigned(..)
  , Index (..)
  ) where

import Types

newtype (NaturalT nT) => Signed nT = Signed Integer

newtype (NaturalT nT) => Unsigned nT = Unsigned Integer

newtype (NaturalT upper) => Index upper = Index Integer