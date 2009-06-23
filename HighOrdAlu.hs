module HighOrdAlu where

import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import Bits
import Types
import Data.Param.TFVec
import Data.RangedWord

constant :: e -> Op D4 e
constant e a b =
  e +> (e +> (e +> singleton e))

inv = hwnot

invop :: Op n Bit
invop a b = map inv a

type Op n e = (TFVec n e -> TFVec n e -> TFVec n e)
type Opcode = Bit

alu :: Op n e -> Op n e -> Opcode -> TFVec n e -> TFVec n e -> TFVec n e
alu op1 op2 opc a b =
  case opc of
    Low -> op1 a b
    High -> op2 a b

zero_inv_alu :: Opcode -> TFVec D4 Bit -> TFVec D4 Bit -> TFVec D4 Bit
zero_inv_alu = alu (constant Low) invop
