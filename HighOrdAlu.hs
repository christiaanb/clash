module HighOrdAlu where

import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import Bits
import Types
import Data.Param.TFVec
import Data.RangedWord

constant :: NaturalT n => e -> Op n e
constant e a b =
  copy e

invop :: Op n Bit
invop a b = map hwnot a

andop :: Op n Bit
andop a b = zipWith hwand a b

-- Is any bit set?
--anyset :: (PositiveT n) => Op n Bit
anyset :: NaturalT n => Op n Bit
--anyset a b = copy undefined (a' `hwor` b')
anyset a b = constant (a' `hwor` b') a b
  where 
    a' = foldl hwor Low a
    b' = foldl hwor Low b

type Op n e = (TFVec n e -> TFVec n e -> TFVec n e)
type Opcode = Bit

alu :: Op n e -> Op n e -> Opcode -> TFVec n e -> TFVec n e -> TFVec n e
alu op1 op2 opc a b =
  case opc of
    Low -> op1 a b
    High -> op2 a b

actual_alu :: Opcode -> TFVec D4 Bit -> TFVec D4 Bit -> TFVec D4 Bit
--actual_alu = alu (constant Low) andop
actual_alu = alu anyset andop
