module Alu  where
import Bits
import qualified Sim

main = Sim.simulate exec program initial_state
mainIO = Sim.simulateIO exec initial_state

dontcare = Low

program = [
            -- (addr, we, op)
            (High, Low, High), -- z = r1 and t (0) ; t = r1 (1)
            (Low, Low, Low), -- z = r0 or t (1); t = r0 (0)
            (Low, High, dontcare), -- r0 = z (1)
            (High, Low, High), -- z = r1 and t (0); t = r1 (1)
            (High, High, dontcare) -- r1 = z (0)
          ]

initial_state = (Regs Low High, Low, Low)

-- Register bank

type RegAddr = Bit
--type RegisterBankState = (Bit, Bit)
data RegisterBankState = Regs { r0, r1 :: Bit} deriving (Show)

register_bank :: 
  (RegAddr, Bit, Bit) -> -- (addr, we, d)
  RegisterBankState -> -- s
  (RegisterBankState, Bit) -- (s', o)

register_bank (Low, Low, _) s = -- Read r0
  (s, r0 s)

register_bank (High, Low, _) s = -- Read r1
  (s, r1 s)

register_bank (addr, High, d) s = -- Write
  (s', dontcare)
  where
    Regs r0 r1 = s
    r0' = if addr == Low then d else r0
    r1' = if addr == High then d else r1
    s' = Regs r0' r1'

-- ALU

type AluOp = Bit

alu :: AluOp -> Bit -> Bit -> Bit
alu High a b = a `hwand` b
alu Low a b = a `hwor` b

type ExecState = (RegisterBankState, Bit, Bit)
exec :: (RegAddr, Bit, AluOp) -> ExecState -> (ExecState, ())

-- Read & Exec
exec (addr, Low, op) s =
  (s', ())
  where
    (reg_s, t, z) = s
    (reg_s', t') = register_bank (addr, Low, dontcare) reg_s
    z' = alu op t' t
    s' = (reg_s', t', z')

-- Write
exec (addr, High, op) s =
  (s', ())
  where
    (reg_s, t, z) = s
    (reg_s', _) = register_bank (addr, High, z) reg_s
    s' = (reg_s', t, z)

-- vim: set ts=8 sw=2 sts=2 expandtab:
