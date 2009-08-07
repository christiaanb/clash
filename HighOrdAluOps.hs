module HighOrdAluOps where

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