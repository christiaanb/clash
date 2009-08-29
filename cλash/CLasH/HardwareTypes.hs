{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, FlexibleContexts, TypeFamilies, TypeOperators #-}

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
  , resizeInt
  , resizeWord
  , hwand
  , hwor
  , hwxor
  , hwnot
  , RAM
  , MemState
  , blockRAM
  ) where

import qualified Prelude as P
import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import Types
import qualified Data.Param.TFVec as TFVec
import Data.Param.TFVec hiding (TFVec)
import Data.RangedWord
import qualified Data.SizedInt as SizedInt
import Data.SizedInt hiding (resize)
import qualified Data.SizedWord as SizedWord
import Data.SizedWord hiding (resize) 

import Language.Haskell.TH.Lift
import Data.Typeable

newtype State s = State s deriving (P.Show)

type Vector = TFVec.TFVec

resizeInt :: (NaturalT nT, NaturalT nT') => SizedInt nT -> SizedInt nT'
resizeInt = SizedInt.resize

resizeWord :: (NaturalT nT, NaturalT nT') => SizedWord nT -> SizedWord nT'
resizeWord = SizedWord.resize

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

type RAM s a          = Vector (s :+: D1) a

type MemState s a      = State (RAM s a)

blockRAM :: 
  (NaturalT s
  ,PositiveT (s :+: D1)
  ,((s :+: D1) :>: s) ~ True ) =>
  (MemState s a) -> 
  a ->
  RangedWord s ->
  RangedWord s ->
  Bool -> 
  ((MemState s a), a )
blockRAM (State mem) data_in rdaddr wraddr wrenable = 
  ((State mem'), data_out)
  where
    data_out  = mem!rdaddr
    -- Only write data_in to memory if write is enabled
    mem' =  if wrenable then
              replace mem wraddr data_in
            else
              mem
