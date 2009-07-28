{-# LANGUAGE TemplateHaskell #-}

module HighOrdAlu where

import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import Bits
import Types
import Data.Param.TFVec
import Data.RangedWord
import CLasH.Translator.Annotations

constant :: e -> Op D4 e
constant e a b =
  (e +> (e +> (e +> (singleton e))))

invop :: Op n Bit
invop a b = map hwnot a

andop :: Op n Bit
andop a b = zipWith hwand a b

-- Is any bit set?
--anyset :: (PositiveT n) => Op n Bit
anyset :: (Bit -> Bit -> Bit) -> Op D4 Bit
--anyset a b = copy undefined (a' `hwor` b')
anyset f a b = constant (a' `hwor` b') a b
  where 
    a' = foldl f Low a
    b' = foldl f Low b

xhwor = hwor

type Op n e = (TFVec n e -> TFVec n e -> TFVec n e)
type Opcode = Bit

{-# ANN sim_input TestInput#-}
sim_input = [ (High,$(vectorTH [High,Low,Low,Low]),$(vectorTH [High,Low,Low,Low]))
            , (High,$(vectorTH [High,High,High,High]),$(vectorTH [High,High,High,High]))
            , (Low,$(vectorTH [High,Low,Low,High]),$(vectorTH [High,Low,High,Low]))]

{-# ANN actual_alu InitState #-}
initstate = High

alu :: Op n e -> Op n e -> Opcode -> TFVec n e -> TFVec n e -> TFVec n e
alu op1 op2 opc a b =
  case opc of
    Low -> op1 a b
    High -> op2 a b

{-# ANN actual_alu TopEntity #-}
actual_alu :: (Opcode, TFVec D4 Bit, TFVec D4 Bit) -> TFVec D4 Bit
--actual_alu = alu (constant Low) andop
actual_alu (opc, a, b) = alu (anyset xhwor) (andop) opc a b
