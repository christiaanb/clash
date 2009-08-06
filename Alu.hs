module Alu  where
import Bits
import qualified Sim
import Data.SizedWord
import Types
import Types.Data.Num
import CLasH.Translator.Annotations
import qualified Prelude as P

fst (a, b) = a
snd (a, b) = b

main = Sim.simulate exec program initial_state
mainIO = Sim.simulateIO exec initial_state

dontcare = Low

newtype State s = State s deriving (P.Show)

program = [
            -- (addr, we, op)
            (High, Low, High), -- z = r1 and t (0) ; t = r1 (1)
            (Low, Low, Low), -- z = r0 or t (1); t = r0 (0)
            (Low, High, dontcare), -- r0 = z (1)
            (High, Low, High), -- z = r1 and t (0); t = r1 (1)
            (High, High, dontcare) -- r1 = z (0)
          ]

--initial_state = (Regs Low High, Low, Low)
initial_state = State (State (0, 1), 0, 0)

type Word = SizedWord D4
-- Register bank
type RegAddr = Bit
type RegisterBankState = State (Word, Word)
--data RegisterBankState = Regs { r0, r1 :: Bit} deriving (Show)

register_bank :: 
  RegAddr -- ^ Address
  -> Bit -- ^ Write Enable
  -> Word -- ^ Data
  -> RegisterBankState -> -- State
  (RegisterBankState, Word) -- (State', Output)

register_bank addr we d (State s) =
  case we of
    Low -> -- Read
      let
        o = case addr of Low -> fst s; High -> snd s
      in (State s, o) -- Don't change state
    High -> -- Write
      let
        (r0, r1) = s
        r0' = case addr of Low -> d; High -> r0
        r1' = case addr of High -> d; Low -> r1
        s' = (r0', r1')
      in (State s', 0) -- Don't output anything useful

-- ALU

type AluOp = Bit

alu :: AluOp -> Word -> Word -> Word
{-# NOINLINE alu #-}
--alu High a b = a `hwand` b
--alu Low a b = a `hwor` b
alu High a b = a P.+ b
alu Low a b = a P.- b

type ExecState = State (RegisterBankState, Word, Word)
exec :: (RegAddr, Bit, AluOp) -> ExecState -> (ExecState, Word)

{-# ANN exec TopEntity #-}
-- Read & Exec
exec (addr, we, op) (State s) =
  (State s', z')
  where
    (reg_s, t, z) = s
    (reg_s', t') = register_bank addr we z reg_s
    z' = alu op t' t
    s' = (reg_s', t', z')

-- vim: set ts=8 sw=2 sts=2 expandtab:
