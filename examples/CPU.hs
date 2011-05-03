module CPU where

import CLasH.HardwareTypes

type Word     = Signed D16
type CpuState = State (Vector D4 Word)

fu op inputs (a1, a2) = 
  op (inputs!a1) (inputs!a2)

fu1 = fu (+)
fu2 = fu (-)
fu3 = fu (*)

data Opcode = ShiftL | Xor | Equal

multiop ShiftL  = shiftL
multiop Xor     = xor
multiop Equal   = \a b -> if a == b then 1 else 0

fu0 c = fu (multiop c)

cpuA :: CpuState 
  -> (Word, Opcode, Vector D4 (Index D7, Index D7))
  -> (CpuState, Word)
cpuA (State s) (x,opc,addrs) = (State s', out)
  where
    inputs  = x +> (0 +> (1 +> s))
    s'      = (fu0 opc inputs (addrs!0)) +> (
              (fu1     inputs (addrs!1)) +> (
              (fu2     inputs (addrs!2)) +> (
              singleton ((fu3     inputs (addrs!3))))))
    out     = vlast s

cpuState :: Vector D4 Word
cpuState = vcopy 0

{-# ANN cpu TopEntity #-}
cpu = cpuA ^^^ cpuState
