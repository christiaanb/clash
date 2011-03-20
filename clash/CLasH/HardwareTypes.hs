{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}

module CLasH.HardwareTypes
  ( module Types
  , module Data.Param.Integer
  , module Data.Param.Vector
  , module Data.Param.Index
  , module Data.Param.Signed
  , module Data.Param.Unsigned
  , module Data.Bits
  , module Language.Haskell.TH.Lift
  , module Control.Category
  , module Control.Arrow
  , module Control.Monad.Fix
  , module CLasH.Translator.Annotations
  , Bit(..)
  , State(..)
  , hwand
  , hwor
  , hwxor
  , hwnot
  , RAM
  , MemState
  , blockRAM
  , Clock(..)
  , Comp
  , simulate
  , (^^^)
  , comp
  , bv2u
  , u2bv
  , s2bv
  , bv2s
  ) where

import Types
import Data.Param.Integer (HWBits(..))
import Data.Param.Vector
import Data.Param.Index
import Data.Param.Signed
import Data.Param.Unsigned 
import Data.Bits hiding (shiftL,shiftR)
import qualified Data.Bits as B

import Language.Haskell.TH.Lift
import Data.Typeable

import Control.Category (Category,(.),id)
import Control.Arrow (Arrow,arr,first,ArrowLoop,loop,(>>>),second,returnA)
import Control.Monad.Fix (mfix)
import qualified Prelude as P
import Prelude hiding (id, (.))
import qualified Data.Set as Set

import CLasH.Translator.Annotations

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
_    `hwand` _    = Low

Low  `hwor` Low   = Low
_    `hwor` _     = High

High `hwxor` Low  = High
Low  `hwxor` High = High
_    `hwxor` _    = Low

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
              vreplace mem wraddr data_in
            else
              mem

-- ==============================
-- = Integer/Vector Conversions =
-- ==============================
-- ===============
-- = Conversions =
-- ===============
bv2u :: NaturalT nT => Vector nT Bit -> Unsigned nT
bv2u bv = vfoldl (\a b -> let
                      a' = B.shiftL a 1
                    in
                      if b == High then
                        a' + 1
                      else
                        a'
                 ) 0 bv

bv2s :: NaturalT nT => Vector nT Bit -> Signed nT
bv2s bv = vfoldl (\a b -> let
                        a' = B.shiftL a 1
                      in
                        if b == High then
                          a' + 1
                        else
                          a'
                   ) 0 bv

u2bv :: NaturalT nT => Unsigned nT -> Vector nT Bit
u2bv u = vreverse . (vmap fst) . (vgenerate f) $ (Low,(0,u))
  where
    f (_,(n,u)) = if testBit u n then (High,(n+1,u)) else (Low,(n+1,u))
    
s2bv :: NaturalT nT => Signed nT -> Vector nT Bit
s2bv u = vreverse . (vmap fst) . (vgenerate f) $ (Low,(0,u))
  where
    f (_,(n,u)) = if testBit u n then (High,(n+1,u)) else (Low,(n+1,u))

-- ==========
-- = Clocks =
-- ==========
data Clock = ClockUp Int | ClockDown Int
  deriving (Eq,Ord,Show)

-- ==================
-- = Automata Arrow =
-- ==================
data Comp i o = C {
    domain :: Set.Set Clock  
  , exec   :: Clock -> i -> (o, Comp i o)
  }

instance Category Comp where
  k@(C { domain = cdA, exec = g}) . (C {domain = cdB, exec = f}) =
     C { domain = Set.union cdA cdB
       , exec   = \clk b -> let (c,f') = f clk b
                                (d,g') = g clk c
                            in (d, g'.f')
       }
  id = arr id

instance Arrow Comp where
  arr f    = C { domain = Set.empty
               , exec   = \clk b -> (f b, arr f)
               }
  first af = af { exec  = \clk (b,d) -> let (c,f') = (exec af) clk b
                                        in ((c,d), first f')
                }
instance ArrowLoop Comp where
   loop af = af { exec = (\clk i -> let ((c,d), f') = (exec af) clk (i, d)
                                    in (c, loop f'))
                }

comp :: (State s -> i -> (State s,o)) -> s -> Clock -> Comp i o
comp f initS clk = C { domain = Set.singleton clk
                     , exec = \clk' i -> let (State s,o)      = f (State initS) i
                                             s' | clk == clk' = s
                                                | otherwise   = initS
                                         in (o, comp f s' clk)                                              
                     }

liftS :: s -> (State s -> i -> (State s,o)) -> Comp i o
liftS init f = C {domain = Set.singleton (ClockUp 1), exec = applyS}
   where applyS = \clk i -> let (State s,o) = f (State init) i
                            in (o, liftS s f)

(^^^) :: (State s -> i -> (State s,o)) -> s -> Comp i o
(^^^) f init = liftS init f

simulate :: Comp b c -> [b] -> [c]
simulate af inps = if (Set.size $ domain af) < 2 then
    simulate' af (Set.findMin $ domain af) inps
  else
    error "Use simulateM for components with more than 1 clock"

simulate' :: Comp b c -> Clock -> [b] -> [c]
simulate' af             _   []     = []
simulate' (C {exec = f}) clk (i:is) = let (o,f') = f clk i in (o : simulate' f' clk is)
