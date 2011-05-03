{-# LANGUAGE Arrows #-}
module Alu where

import CLasH.HardwareTypes

dontcare = Low

program = [
         -- (addr, we  , op      )
            (High, Low , High    ), -- z = r1 and t (0) ; t = r1 (1)
            (Low , Low , Low     ), -- z = r0 or t (1); t = r0 (0)
            (Low , High, dontcare), -- r0 = z (1)
            (High, Low , High    ), -- z = r1 and t (0); t = r1 (1)
            (High, High, dontcare)  -- r1 = z (0)
          ]

-- --initial_state = (Regs Low High, Low, Low)
-- initial_state = State (State (0, 1), 0, 0)

type Word = Unsigned D4

-- Register bank
type RegAddr = Bit
type RegisterBankState = State (Word, Word)

register_bank ::
  RegisterBankState ->      -- ^ State
  (RegAddr, Bit, Word) ->   -- ^ (Address, Write Enable, Data)
  (RegisterBankState, Word) -- ^ (State', Output)

register_bank (State s) (addr, we, d) = (State s', o)
  where
    s' = case we of
      Low -> s -- Read
      High -> -- Write
        let
          (r0, r1) = s
          r0' = case addr of Low -> d; High -> r0
          r1' = case addr of High -> d; Low -> r1
        in (r0', r1')
    o = case we of
      -- Read
      Low -> case addr of Low -> fst s; High -> snd s
      -- Write
      High -> 0 -- Don't output anything useful

-- ALU

type AluOp = Bit

alu :: AluOp -> Word -> Word -> Word
alu High a b = a + b
alu Low a b  = a - b

delayN (State s) inp = (State (inp +>> s), vlast s)

{-# ANN exec TopEntity #-}
exec = proc (addr,we,op) -> do
  rec
    (t,z) <- delayN ^^^ (singleton (0,0)) -< (t',z')
    t'    <- register_bank ^^^ (0,1)     -< (addr,we,z)
    z'    <- arr (\(a,b,c) -> alu a b c) -< (op, t', t)
  returnA -< z'
