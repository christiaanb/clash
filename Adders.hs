{-# LANGUAGE TemplateHaskell #-}

module Adders where
import Bits
import qualified Sim

import qualified Prelude as P
import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )

import Language.Haskell.Syntax
import Types
import Data.Param.TFVec
import Data.RangedWord
import Data.SizedInt
import Data.SizedWord

mainIO f = Sim.simulateIO (Sim.stateless f) ()

-- This function is from Sim.hs, but we redefine it here so it can get inlined
-- by default.
stateless :: (i -> o) -> (i -> () -> ((), o))
stateless f = \i s -> (s, f i)

show_add f = do print ("Sum:   " P.++ (displaysigs s)); print ("Carry: " P.++ (displaysig c))
  where
    a = [High, High, High, High]
    b = [Low, Low, Low, High]
    (s, c) = f (a, b)

mux2 :: Bit -> (Bit, Bit) -> Bit
mux2 Low (a, b) = a
mux2 High (a, b) = b

-- Not really an adder, but this is nice minimal hardware description
wire :: Bit -> Bit
wire a = a

-- bus :: (TypeLevel.Pos len) => BitVec len -> BitVec len
bus v = v

-- bus_4 :: BitVec TypeLevel.D4 -> BitVec TypeLevel.D4
bus_4 v = v

{-
inv_n :: (Pos len) => BitVec len -> BitVec len
inv_n v =
  --FSVec.map hwnot v
  inv_n_rec v

class Inv vec where
  inv_n_rec :: vec -> vec

instance (Pos len) => Inv (BitVec len) where
  inv_n_rec v = 
    h FSVec.+> t
    where
      h = FSVec.head v
      t = FSVec.tail v

instance Inv (BitVec D0) where
  inv_n_rec v = v
-}
-- Not really an adder either, but a slightly more complex example
inv :: Bit -> Bit
inv a = let r = hwnot a in r

-- Not really an adder either, but a slightly more complex example
invinv :: Bit -> Bit
invinv a = hwnot (hwnot a)

-- Not really an adder either, but a slightly more complex example
dup :: Bit -> (Bit, Bit)
dup a = (a, a)

-- Not really an adder either, but a simple stateful example (D-flipflop)
dff :: Bit -> Bit -> (Bit, Bit)
dff d s = (s', q)
  where
    q = s
    s' = d

type ShifterState = (Bit, Bit, Bit, Bit)
shifter :: Bit -> ShifterState -> (ShifterState, Bit)
shifter i (a, b, c, d) =
  (s', d)
  where
    s' = (i, a, b, c)

{-# NOINLINE shifter_en #-}
shifter_en :: Bit -> Bit-> ShifterState -> (ShifterState, Bit)
shifter_en High i (a, b, c, d) =
  (s', d)
  where
    s' = (i, a, b, c)

shifter_en Low i s@(a, b, c, d) =
  (s, d)

-- Two multiplexed shifters
type ShiftersState = (ShifterState, ShifterState)
shifters :: Bit -> Bit -> ShiftersState -> (ShiftersState, Bit)
shifters sel i (sa, sb) =
  (s', out)
  where
    (sa', outa) = shifter_en sel i sa
    (sb', outb) = shifter_en (hwnot sel) i sb
    s' = (sa', sb')
    out = if sel == High then outa else outb

-- Combinatoric stateless no-carry adder
-- A -> B -> S
no_carry_adder :: (Bit, Bit) -> Bit
no_carry_adder (a, b) = a `hwxor` b

-- Combinatoric stateless half adder
-- A -> B -> (S, C)
half_adder :: (Bit, Bit) -> (Bit, Bit)
{-# NOINLINE half_adder #-}
half_adder (a, b) = 
  ( a `hwxor` b, a `hwand` b )

-- Combinatoric stateless full adder
-- (A, B, C) -> (S, C)
full_adder :: (Bit, Bit, Bit) -> (Bit, Bit)
full_adder (a, b, cin) = (s, c)
  where
    (s1, c1) = half_adder(a, b)
    (s, c2)  = half_adder(s1, cin)
    c        = c1 `hwor` c2

sfull_adder = stateless full_adder

-- Four bit adder
-- Explicit version
-- [a] -> [b] -> ([s], cout)
exp_adder :: ([Bit], [Bit]) -> ([Bit], Bit)

exp_adder ([a3,a2,a1,a0], [b3,b2,b1,b0]) =
  ([s3, s2, s1, s0], c3)
  where
    (s0, c0) = full_adder (a0, b0, Low)
    (s1, c1) = full_adder (a1, b1, c0)
    (s2, c2) = full_adder (a2, b2, c1)
    (s3, c3) = full_adder (a3, b3, c2)

-- Any number of bits adder
-- Recursive version
-- [a] -> [b] -> ([s], cout)
rec_adder :: ([Bit], [Bit]) -> ([Bit], Bit)

rec_adder ([], []) = ([], Low)
rec_adder ((a:as), (b:bs)) = 
  (s : rest, cout)
  where
    (rest, cin) = rec_adder (as, bs)
    (s, cout) = full_adder (a, b, cin)

foo = id
add, sub :: Int -> Int -> Int
add a b = a + b
sub a b = a - b

highordtest = \x ->
  let s = foo x
  in
     case s of
       (a, b) ->
         case a of
           High -> add
           Low -> let
             op' = case b of
                High -> sub
                Low -> \c d -> c
             in
                \c d -> op' d c

xand a b = hwand a b

functiontest :: TFVec D3 (TFVec D4 Bit) -> TFVec D12 Bit
functiontest = \v -> let r = concat v in r

functiontest2 :: SizedInt D8 -> SizedInt D8
functiontest2 = \a -> let r = a + 1 in r

xhwnot x = hwnot x

maptest :: TFVec D4 Bit -> TFVec D4 Bit
maptest = \v -> let r = map xhwnot v in r

highordtest2 = \a b ->
         case a of
           High -> \c d -> d
           Low -> let
             op' :: Bit -> Bit -> Bit
             op' = case b of
                High -> \c d -> d
                Low -> \c d -> c
             in
                \c d -> op' d c
-- Four bit adder, using the continous adder below
-- [a] -> [b] -> ([s], cout)
con_adder_4 as bs = 
 ([s3, s2, s1, s0], c)
 where
   ((s0, _):(s1, _):(s2, _):(s3, c):_) = con_adder (P.zip ((P.reverse as) P.++ lows) ((P.reverse bs) P.++ lows))

-- Continuous sequential version
-- Stream a -> Stream b -> Stream (sum, cout)
con_adder :: Stream (Bit, Bit) -> Stream (Bit, Bit)

-- Forward to con_adder_int, but supply an initial state
con_adder pin =
 con_adder_int pin Low

-- Stream a -> Stream b -> state -> Stream (s, c)
con_adder_int :: Stream (Bit, Bit) -> Bit -> Stream (Bit, Bit)
con_adder_int ((a,b):rest) cin =
 (s, cout) : con_adder_int rest cout
 where
   (s, cout) = full_adder (a, b, cin)

-- vim: set ts=8 sw=2 sts=2 expandtab:
