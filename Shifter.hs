module Shifter (main, mainIO) where
import Bits
import qualified Sim

main = Sim.simulate shifter [High, Low, Low, Low] [High, Low, High, Low]
mainIO = Sim.simulateIO shifter [High, Low, High, Low]

type ShifterState = [Bit]
shifter :: Bit -> ShifterState -> (ShifterState, Bit)
shifter i s =
  (s', o)
  where
    s' = (o `hwxor` i) : (init s)
    o  = last s

-- vim: set ts=8 sw=2 sts=2 expandtab:
