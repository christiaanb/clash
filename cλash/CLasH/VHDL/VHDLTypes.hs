--
-- Some types used by the VHDL module.
--
{-# LANGUAGE TemplateHaskell #-}
module CLasH.VHDL.VHDLTypes where

-- Standard imports
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import Data.Accessor
import qualified Data.Accessor.Template

-- GHC API imports
import qualified HscTypes

-- ForSyDe imports
import qualified Language.VHDL.AST as AST

-- Local imports

-- A description of a port of an entity
type Port = (AST.VHDLId, AST.TypeMark)

-- A description of a VHDL entity. Contains both the entity itself as well as
-- info on how to map a haskell value (argument / result) on to the entity's
-- ports.
data Entity = Entity { 
  ent_id     :: AST.VHDLId,           -- The id of the entity
  ent_args   :: [Port],      -- A mapping of each function argument to port names
  ent_res    :: Port,         -- A mapping of the function result to port names
  ent_dec    :: AST.EntityDec -- ^ The complete entity declaration
} deriving (Show);

type Architecture = AST.ArchBody

-- vim: set ts=8 sw=2 sts=2 expandtab:
