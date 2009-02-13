--
-- Some types used by the VHDL module.
--
module VHDLTypes where

import qualified ForSyDe.Backend.VHDL.AST as AST

import FlattenTypes

type VHDLSignalMap = SignalMap AST.VHDLId

-- A description of a VHDL entity. Contains both the entity itself as well as
-- info on how to map a haskell value (argument / result) on to the entity's
-- ports.
data Entity = Entity {
  ent_args   :: [VHDLSignalMap],      -- A mapping of each function argument to port names
  ent_res    :: VHDLSignalMap,        -- A mapping of the function result to port names
  ent_decl   :: Maybe AST.EntityDec   -- The actual entity declaration. Can be empty for builtin functions.
}
