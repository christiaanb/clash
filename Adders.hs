module Adders where
import Bits
import Language.Haskell.Syntax

main = do show_add exp_adder; show_add rec_adder;

show_add f = do print ("Sum:   " ++ (displaysigs s)); print ("Carry: " ++ (displaysig c))
  where
    a = [High, High, High, High]
    b = [Low, Low, Low, High]
    (s, c) = f (a, b)

-- Not really an adder, but this is nice minimal hardware description
wire :: Bit -> Bit
wire a = a

-- Not really an adder either, but a slightly more complex example
inv :: Bit -> Bit
inv a = hwnot a

-- Not really an adder either, but a slightly more complex example
invinv :: Bit -> Bit
invinv a = hwnot (hwnot a)

-- Not really an adder either, but a slightly more complex example
dup :: Bit -> (Bit, Bit)
dup a = (a, a)

-- Combinatoric stateless no-carry adder
-- A -> B -> S
no_carry_adder :: (Bit, Bit) -> Bit
no_carry_adder (a, b) = a `hwxor` b

-- Combinatoric stateless half adder
-- A -> B -> (S, C)
half_adder :: (Bit, Bit) -> (Bit, Bit)
half_adder (a, b) = 
  ( a `hwxor` b, a `hwand` b )

-- Combinatoric stateless full adder
-- (A, B, C) -> (S, C)
full_adder :: (Bit, Bit, Bit) -> (Bit, Bit)
full_adder (a, b, cin) = (s, c)
  where
    s = a `hwxor` b `hwxor` cin
    c = a `hwand` b `hwor` (cin `hwand` (a `hwxor` b))

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

-- Four bit adder, using the continous adder below
-- [a] -> [b] -> ([s], cout)
--con_adder_4 as bs = 
--  ([s3, s2, s1, s0], c)
--  where
--    ((s0, _):(s1, _):(s2, _):(s3, c):_) = con_adder (zip ((reverse as) ++ lows) ((reverse bs) ++ lows))

-- Continuous sequential version
-- Stream a -> Stream b -> Stream (sum, cout)
--con_adder :: Stream (Bit, Bit) -> Stream (Bit, Bit)

-- Forward to con_adder_int, but supply an initial state
--con_adder pin =
--  con_adder_int pin Low

-- Stream a -> Stream b -> state -> Stream (s, c)
--con_adder_int :: Stream (Bit, Bit) -> Bit -> Stream (Bit, Bit)
--con_adder_int ((a,b):rest) cin =
--  (s, cout) : con_adder_int rest cout
--  where
--    (s, cout) = full_adder a b cin

-- vim: set ts=8 sw=2 sts=2 expandtab:
