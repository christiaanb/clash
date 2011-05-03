{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, RecordWildCards #-}

module CLasH.HardwareTypes
  ( module Types
  , module Data.Param.Integer
  , module Data.Param.Vector
  , module Data.Param.Index
  , module Data.Param.Signed
  , module Data.Param.Unsigned
  , module Data.Bits
  , module Language.Haskell.TH.Lift
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
  , pulseLength
  , Comp
  , simulate
  , (^^^)
  , comp
  , bv2u
  , u2bv
  , s2bv
  , bv2s
  , SimulatorSession
  , SimulationState
  , simulateM
  , run
  , runWithClock
  , setInput
  , setAndRun
  , getOutput
  , showOutput
  , assert
  , report
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
import Control.Arrow (Arrow,arr,first,ArrowLoop,loop,(>>>),returnA)
import Control.Monad.Fix (mfix)
import qualified Prelude as P
import Prelude hiding (id, (.))
import qualified Data.Set as Set

import qualified Data.List as L

import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Accessor.Template
import qualified Data.Accessor.Monad.Trans.StrictState as MonadState
import qualified Control.Monad.Trans.Class as Trans

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

pulseLength (ClockUp   i) = i
pulseLength (ClockDown i) = i

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

data SimulationState i o = SimulationState {
    clockTicks_ :: ([Clock],[Int])
  , input_      :: i
  , hw_         :: Comp i o
  }
  
Data.Accessor.Template.deriveAccessors ''SimulationState

type SimulatorSession i o a = State.StateT (SimulationState i o) IO a

simulateM :: Comp i o -> SimulatorSession i o () -> IO ()
simulateM hw testbench = State.evalStateT testbench initSession
  where
    initSession = SimulationState ((Set.toList $ domain hw), (replicate (Set.size $ domain hw) 1)) (error "CLasH.simulateM: initial simulation input not set") hw


run :: Int -> SimulatorSession i o ()
run n = do
  (clocks,ticks) <- MonadState.get clockTicks
  let (pulses,newTicks) = runClocks (clocks,ticks) n
  MonadState.modify clockTicks (\(a,b) -> (a,newTicks))
  curInp <- MonadState.get input
  MonadState.modify hw (snd . (run' pulses curInp))

runWithClock :: Clock -> Int -> SimulatorSession i o ()
runWithClock clk n = do
  curInp <- MonadState.get input
  MonadState.modify hw (snd . (run' (replicate n clk) curInp))
  
run' []         _ arch     = ([],arch)
run' (clk:clks) i (C {..}) = let (c,f')   = clk `seq` exec clk i
                                 (cs,f'') = f' `seq` run' clks i f'
                             in f'' `seq` (c:cs,f'')

setInput :: i -> SimulatorSession i o ()
setInput i = MonadState.set input i

setAndRun :: i -> Int -> SimulatorSession i o ()
setAndRun inp n = (setInput inp) >> (run n)

getOutput :: SimulatorSession i o o
getOutput = do
  curInp <- MonadState.get input
  arch <- MonadState.get hw
  return $ head $ fst $ run' [ClockUp (-1)] curInp arch

showOutput :: (Show o) => SimulatorSession i o ()
showOutput = do
  outp <- getOutput
  Trans.lift $ putStrLn $ show outp
  
assert :: (o -> Bool) -> String -> SimulatorSession i o ()
assert test msg = do
  outp <- getOutput
  if (test outp) then return () else Trans.lift $ putStrLn msg

report :: String -> SimulatorSession i o ()
report msg = Trans.lift $ putStrLn msg

runClocks :: ([Clock], [Int]) -> Int -> ([Clock],[Int])
runClocks (clocks, ticks) 0     = ([],ticks)
runClocks (clocks, ticks) delta = ((concat curClocks) ++ nextClocks,nextTicks)
  where
    (curClocks,curTicks)   = unzip $ zipWith clockTick clocks ticks
    (nextClocks,nextTicks) = runClocks (clocks,curTicks) (delta-1)

clockTick (ClockUp   i) i' = if i == i' then ([ClockUp i]  ,1) else ([],i'+1)
clockTick (ClockDown i) i' = if i == i' then ([ClockDown i],1) else ([],i'+1)


