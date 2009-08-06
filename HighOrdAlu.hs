{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, NoImplicitPrelude #-}

module HighOrdAlu where

import qualified Prelude as P
import CLasH.HardwareTypes
import CLasH.Translator.Annotations

constant :: NaturalT n => e -> Op n e
constant e a b = copy e

invop :: Op n Bit
invop a b = map hwnot a

andop :: (e -> e -> e) -> Op n e
andop f a b = zipWith f a b

-- Is any bit set?
--anyset :: (PositiveT n) => Op n Bit
anyset :: NaturalT n => (e -> e -> e) -> e -> Op n e
--anyset a b = copy undefined (a' `hwor` b')
anyset f s a b = constant (f a' b') a b
  where 
    a' = foldl f s a
    b' = foldl f s b

xhwor = hwor

type Op n e = (Vector n e -> Vector n e -> Vector n e)
type Opcode = Bit

{-# ANN sim_input TestInput#-}
sim_input :: [(Opcode, Vector D4 (SizedInt D8), Vector D4 (SizedInt D8))]
sim_input = [ (High,  $(vectorTH ([4,3,2,1]::[SizedInt D8])), $(vectorTH ([1,2,3,4]::[SizedInt D8])))
            , (High,  $(vectorTH ([4,3,2,1]::[SizedInt D8])), $(vectorTH ([1,2,3,4]::[SizedInt D8])))
            , (Low,   $(vectorTH ([4,3,2,1]::[SizedInt D8])), $(vectorTH ([1,2,3,4]::[SizedInt D8]))) ]

{-# ANN actual_alu InitState #-}
initstate = High

alu :: Op n e -> Op n e -> Opcode -> Vector n e -> Vector n e -> Vector n e
alu op1 op2 opc a b =
  case opc of
    Low -> op1 a b
    High -> op2 a b

{-# ANN actual_alu TopEntity #-}
actual_alu :: (Opcode, Vector D4 (SizedInt D8), Vector D4 (SizedInt D8)) -> Vector D4 (SizedInt D8)
--actual_alu = alu (constant Low) andop
actual_alu (opc, a, b) = alu (anyset (+) (0 :: SizedInt D8)) (andop (-)) opc a b

runalu = P.map actual_alu sim_input