--
-- Some types used by the VHDL module.
--
module CLasH.VHDL.VHDLTypes where

-- VHDL imports
import qualified Language.VHDL.AST as AST

-- A description of a port of an entity
type Port = (AST.VHDLId, AST.TypeMark)

-- A description of a VHDL entity. Contains both the entity itself as well as
-- info on how to map a haskell value (argument / result) on to the entity's
-- ports.
data Entity = Entity { 
  ent_id     :: AST.VHDLId, -- ^ The id of the entity
  ent_args   :: [Port], -- ^ A port for each non-empty function argument
  ent_res    :: Maybe Port, -- ^ The output port
  ent_dec    :: AST.EntityDec -- ^ The complete entity declaration
} deriving (Show);

type Architecture = AST.ArchBody

-- vim: set ts=8 sw=2 sts=2 expandtab:
