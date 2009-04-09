module Alu  where
import Bits
import qualified Sim
import Data.SizedWord
import Types.Data.Num

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

--initial_state = (Regs Low High, Low, Low)
initial_state = ((0, 1), 0, 0)

type Word = SizedWord D4
-- Register bank
type RegAddr = Bit
type RegisterBankState = (Word, Word)
--data RegisterBankState = Regs { r0, r1 :: Bit} deriving (Show)

register_bank :: 
  (RegAddr, Bit, Word) -> -- (addr, we, d)
  RegisterBankState -> -- s
  (RegisterBankState, Word) -- (s', o)

register_bank (Low, Low, _) s = -- Read r0
  --(s, r0 s)
  (s, fst s)

register_bank (High, Low, _) s = -- Read r1
  --(s, r1 s)
  (s, snd s)

register_bank (addr, High, d) s = -- Write
  (s', 0)
  where
    --Regs r0 r1 = s
    (r0, r1) = s
    r0' = case addr of Low -> d; High -> r0
    r1' = case addr of High -> d; Low -> r1
    --s' = Regs r0' r1'
    s' = (r0', r1')

-- ALU

type AluOp = Bit

alu :: AluOp -> Word -> Word -> Word
{-# NOINLINE alu #-}
--alu High a b = a `hwand` b
--alu Low a b = a `hwor` b
alu High a b = a
alu Low a b = b

type ExecState = (RegisterBankState, Word, Word)
exec :: (RegAddr, Bit, AluOp) -> ExecState -> (ExecState, Word)

-- Read & Exec
exec (addr, we, op) s =
  (s', z')
  where
    (reg_s, t, z) = s
    (reg_s', t') = register_bank (addr, we, z) reg_s
    z' = alu op t' t
    s' = (reg_s', t', z')

-- vim: set ts=8 sw=2 sts=2 expandtab:
