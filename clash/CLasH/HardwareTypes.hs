{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}

module CLasH.HardwareTypes
  ( module Types
  , module Data.Param.Integer
  , module Data.Param.Vector
  , module Data.Param.Index
  , module Data.Param.Signed
  , module Data.Param.Unsigned
  , module Prelude
  , module Data.Bits
  , module Language.Haskell.TH.Lift
  , Bit(..)
  , State(..)
  , hwand
  , hwor
  , hwxor
  , hwnot
  , RAM
  , MemState
  , blockRAM
  ) where

import qualified Prelude as P
import Prelude (Bool(..),Num(..),Eq(..),Ord(..),snd,fst,otherwise,(&&),(||),not)
import Types
import Data.Param.Integer (HWBits(..))
import Data.Param.Vector
import Data.Param.Index
import Data.Param.Signed
import Data.Param.Unsigned 
import Data.Bits hiding (shiftL,shiftR)

import Language.Haskell.TH.Lift
import Data.Typeable

newtype State s = State s deriving (P.Show)

-- The plain Bit type
data Bit = High | Low
  deriving (P.Show, Eq, P.Read, Typeable)

deriveLift ''Bit

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

type RAM s a          = Vector s a
type MemState s a     = State (RAM s a)

blockRAM :: 
  PositiveT s  =>
  MemState s a -> 
  a ->
  Index s ->
  Index s ->
  Bool -> 
  (MemState s a, a )
blockRAM (State mem) data_in rdaddr wraddr wrenable = 
  ((State mem'), data_out)
  where
    data_out  = mem!rdaddr
    -- Only write data_in to memory if write is enabled
    mem' =  if wrenable then
              replace mem wraddr data_in
            else
              mem
