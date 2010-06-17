{-# LANGUAGE TemplateHaskell #-}

module HigherOrderCPU where

-- hide default prelude functions
import qualified Prelude as P

-- import CλaSH specific types
import CLasH.HardwareTypes
import CLasH.Translator.Annotations

type CpuState = State (Vector D4 (Signed D16))

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

{-# ANN cpu TopEntity #-}
{-# ANN cpu (InitState 'cpuState) #-}
cpu :: CpuState 
  -> (Signed D16, Opcode, Vector D4 (Index D7, Index D7))
  -> (CpuState, Signed D16)
cpu (State s) (x,opc,addrs) = (State s', out)
  where
    inputs  = x +> (0 +> (1 +> s))
    s'      = (fu0 opc inputs (addrs!0)) +> (
              (fu1     inputs (addrs!1)) +> (
              (fu2     inputs (addrs!2)) +> (
              (fu3     inputs (addrs!3)) +> empty)))
    out     = last s

cpuState :: Vector D4 (Signed D16)
cpuState = copy 0
