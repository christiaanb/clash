module Inverter (main) where
import Bits
import qualified Sim

main = Sim.simulate inverter [High, Low, High, Low] ()
mainIO = Sim.simulateIO inverter ()

type InverterState = ()
inverter :: Bit -> InverterState -> (InverterState, Bit)
inverter a s = (s, hwnot a)

-- vim: set ts=8 sw=2 sts=2 expandtab:
