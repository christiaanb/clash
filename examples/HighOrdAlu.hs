{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module HighOrdAlu where

import CLasH.HardwareTypes

import HighOrdAluOps

{-# ANN sim_input TestInput#-}
sim_input :: [(Opcode, Vector D4 (Signed D8), Vector D4 (Signed D8))]
sim_input = [ (High,  $(vTH ([4,3,2,1]::[Signed D8])), $(vTH ([1,2,3,4]::[Signed D8])))
            , (High,  $(vTH ([4,3,2,1]::[Signed D8])), $(vTH ([1,2,3,4]::[Signed D8])))
            , (Low,   $(vTH ([4,3,2,1]::[Signed D8])), $(vTH ([1,2,3,4]::[Signed D8]))) ]

alu :: Op n e -> Op n e -> Opcode -> Vector n e -> Vector n e -> Vector n e
alu op1 op2 opc a b =
  case opc of
    Low  -> op1 a b
    High -> op2 a b

{-# ANN actual_alu TopEntity #-}
actual_alu :: (Opcode, Vector D4 (Signed D8), Vector D4 (Signed D8)) -> Vector D4 (Signed D8)
actual_alu (opc, a, b) = alu (anyset (+) (0 :: Signed D8)) (andop (-)) opc a b

runalu = map actual_alu sim_input
