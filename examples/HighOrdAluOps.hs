module HighOrdAluOps where

import CLasH.HardwareTypes

type Op n e = (Vector n e -> Vector n e -> Vector n e)
type Opcode = Bit

constant :: NaturalT n => e -> Op n e
constant e a b = vcopy e

invop :: Op n Bit
invop a b = vmap hwnot a

andop f a b = vzipWith f a b

-- Is any bit set?
anyset :: NaturalT n => (e -> e -> e) -> e -> Op n e
anyset f s a b = constant (f a' b') a b
  where 
    a' = vfoldl f s a
    b' = vfoldl f s b
