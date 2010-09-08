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
  , module Control.Category
  , module Control.Arrow
  , module Control.Monad.Fix
  , Bit(..)
  , State(..)
  , hwand
  , hwor
  , hwxor
  , hwnot
  , RAM
  , MemState
  , blockRAM
  , Stat
  , simulate
  , (^^^)
  ) where

import qualified Prelude as P
import Prelude (Bool(..),Num(..),Eq(..),Ord(..),snd,fst,otherwise,(&&),(||),not,(>>),(>>=),fail,return)
import Types
import Data.Param.Integer (HWBits(..))
import Data.Param.Vector
import Data.Param.Index
import Data.Param.Signed
import Data.Param.Unsigned 
import Data.Bits hiding (shiftL,shiftR)

import Language.Haskell.TH.Lift
import Data.Typeable

import Control.Category (Category,(.),id)
import Control.Arrow (Arrow,arr,first,ArrowLoop,loop,(>>>),second,returnA)
import Control.Monad.Fix (mfix)

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

-- ==================
-- = Automata Arrow =
-- ==================
newtype Stat i o = A {
     apply :: i -> (o, Stat i o)
}

instance Category Stat where
   (A g) . (A f) = A (\b ->  let (c,f') = f b
                                 (d,g') = g c
                             in (d, g'.f'))
   id = arr id

instance Arrow Stat where
   arr f = A (\b -> (f b, arr f))
   first (A f) = A (\(b,d) -> let (c,f') = f b
                              in ((c,d), first f'))
instance ArrowLoop Stat where
   loop (A f) = A (\i -> let ((c,d), f') = f (i, d)
                         in (c, loop f'))

liftS :: s -> (State s -> i -> (State s,o)) -> Stat i o
liftS init f = A applyS
   where applyS = \i -> let (State s,o) = f (State init) i
                        in (o, liftS s f)

simulate :: Stat b c -> [b] -> [c]
simulate (A f) []     = []
simulate (A f) (b:bs) = let (c,f') = f b in (c : simulate f' bs)

arrState :: s -> (State s -> i -> (State s,o)) -> Stat i o
arrState = liftS

(^^^) :: (State s -> i -> (State s,o)) -> s -> Stat i o
(^^^) f init = arrState init f
