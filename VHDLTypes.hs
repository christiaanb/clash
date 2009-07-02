--
-- Some types used by the VHDL module.
--
{-# LANGUAGE TemplateHaskell #-}
module VHDLTypes where

-- Standard imports
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import Data.Accessor
import qualified Data.Accessor.Template

-- GHC API imports
import qualified Type
import qualified CoreSyn

-- ForSyDe imports
import qualified ForSyDe.Backend.VHDL.AST as AST

-- Local imports

-- A description of a port of an entity
type Port = (AST.VHDLId, AST.TypeMark)

-- A description of a VHDL entity. Contains both the entity itself as well as
-- info on how to map a haskell value (argument / result) on to the entity's
-- ports.
data Entity = Entity { 
  ent_id     :: AST.VHDLId,           -- The id of the entity
  ent_args   :: [Port],      -- A mapping of each function argument to port names
  ent_res    :: Port         -- A mapping of the function result to port names
} deriving (Show);

-- A orderable equivalent of CoreSyn's Type for use as a map key
newtype OrdType = OrdType { getType :: Type.Type }
instance Eq OrdType where
  (OrdType a) == (OrdType b) = Type.tcEqType a b
instance Ord OrdType where
  compare (OrdType a) (OrdType b) = Type.tcCmpType a b

-- A map of a Core type to the corresponding type name
type TypeMap = Map.Map OrdType (AST.VHDLId, Either AST.TypeDef AST.SubtypeIn)

-- A map of a vector Core element type and function name to the coressponding
-- VHDLId of the function and the function body.
type TypeFunMap = Map.Map (OrdType, String) (AST.VHDLId, AST.SubProgBody)

-- A map of a Haskell function to a hardware signature
type SignatureMap = Map.Map CoreSyn.CoreBndr Entity

data VHDLState = VHDLState {
  -- | A map of Core type -> VHDL Type
  vsTypes_      :: TypeMap,
  -- | A list of type declarations
  vsTypeDecls_  :: [AST.PackageDecItem],
  -- | A map of vector Core type -> VHDL type function
  vsTypeFuns_   :: TypeFunMap,
  -- | A map of HsFunction -> hardware signature (entity name, port names,
  --   etc.)
  vsSignatures_ :: SignatureMap
}

-- Derive accessors
$( Data.Accessor.Template.deriveAccessors ''VHDLState )

-- | The state containing a VHDL Session
type VHDLSession = State.State VHDLState

-- | A substate containing just the types
type TypeState = State.State TypeMap

-- A function that generates VHDL for a builtin function
type BuiltinBuilder = 
  (Either CoreSyn.CoreBndr AST.VHDLName) -- ^ The destination signal and it's original type
  -> CoreSyn.CoreBndr -- ^ The function called
  -> [Either CoreSyn.CoreExpr AST.Expr] -- ^ The value arguments passed (excluding type and
                    --   dictionary arguments).
  -> VHDLSession [AST.ConcSm] -- ^ The resulting concurrent statements.

-- A map of a builtin function to VHDL function builder 
type NameTable = Map.Map String (Int, BuiltinBuilder )

-- vim: set ts=8 sw=2 sts=2 expandtab:
