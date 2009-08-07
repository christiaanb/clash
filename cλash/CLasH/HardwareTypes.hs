{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}

module CLasH.HardwareTypes
  ( module Types
  , module Data.Param.TFVec
  , module Data.RangedWord
  , module Data.SizedInt
  , module Data.SizedWord
  , module Prelude
  , Bit(..)
  , State(..)
  , Vector
  , hwand
  , hwor
  , hwxor
  , hwnot
  ) where

import qualified Prelude as P
import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import Types
import qualified Data.Param.TFVec as TFVec
import Data.Param.TFVec hiding (TFVec)
import Data.RangedWord
import Data.SizedInt
import Data.SizedWord 

import Language.Haskell.TH.Lift
import Data.Typeable

newtype State s = State s deriving (P.Show)

type Vector = TFVec.TFVec

-- The plain Bit type
data Bit = High | Low
  deriving (P.Show, P.Eq, P.Read, Typeable)

$(deriveLift1 ''Bit)

hwand :: Bit -> Bit -> Bit
hwor  :: Bit -> Bit -> Bit
hwxor :: Bit -> Bit -> Bit
hwnot :: Bit -> Bit

High `hwand` High = High
_ `hwand` _ = Low

High `hwor` _  = High
_ `hwor` High  = High
Low `hwor` Low = Low

High `hwxor` Low = High
Low `hwxor` High = High
_ `hwxor` _      = Low

hwnot High = Low
hwnot Low  = High