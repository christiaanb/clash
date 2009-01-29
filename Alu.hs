module Alu (main) where
import Bits
import qualified Sim

main = Sim.simulate exec program initial_state
mainIO = Sim.simulateIO exec initial_state

program = [
            -- (addr, we, op)
            (High, Low, High), -- z = r1 and t (0) ; t = r1 (1)
            (Low, Low, Low), -- z = r0 or t (1); t = r0 (0)
            (Low, High, DontCare), -- r0 = z (1)
            (High, Low, High), -- z = r1 and t (0); t = r1 (1)
            (High, High, DontCare) -- r1 = z (0)
          ]

initial_state = ((Low, High), (), Low, Low)

-- Register bank

type RegAddr = Bit
type RegisterBankState = (Bit, Bit)
register_bank :: 
  (RegAddr, Bit, Bit) -> -- (addr, we, d)
  RegisterBankState -> -- s
  (RegisterBankState, Bit) -- (s', o)

register_bank (Low, Low, _) s = -- Read r0
  (s, fst s)

register_bank (High, Low, _) s = -- Read r1
  (s, snd s)

register_bank (addr, High, d) s = -- Write
  (s', DontCare)
  where
    (r0, r1) = s
    r0' = if addr == Low then d else r0
    r1' = if addr == High then d else r1
    s' = (r0', r1')

-- ALU

type AluState = ()
type AluOp = Bit

alu :: (AluOp, Bit, Bit) -> AluState -> (AluState, Bit)
alu (High, a, b) s = ((), a `hwand` b)
alu (Low, a, b) s = ((), a `hwor` b)

type ExecState = (RegisterBankState, AluState, Bit, Bit)
exec :: (RegAddr, Bit, AluOp) -> ExecState -> (ExecState, ())

-- Read & Exec
exec (addr, Low, op) s =
  (s', ())
  where
    (reg_s, alu_s, t, z) = s
    (reg_s', t') = register_bank (addr, Low, DontCare) reg_s
    (alu_s', z') = alu (op, t', t) alu_s
    s' = (reg_s', alu_s', t', z')

-- Write
exec (addr, High, op) s =
  (s', ())
  where
    (reg_s, alu_s, t, z) = s
    (reg_s', _) = register_bank (addr, High, z) reg_s
    s' = (reg_s', alu_s, t, z)

-- vim: set ts=8 sw=2 sts=2 expandtab:
