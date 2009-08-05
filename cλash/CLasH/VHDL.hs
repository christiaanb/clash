--
-- Functions to generate VHDL from FlatFunctions
--
module CLasH.VHDL where

-- Standard modules
import qualified Data.Map as Map
import qualified Maybe
import qualified Control.Monad as Monad
import qualified Control.Arrow as Arrow
import qualified Control.Monad.Trans.State as State
import qualified Data.Monoid as Monoid
import Data.Accessor
import Data.Accessor.MonadState as MonadState
import Debug.Trace

-- ForSyDe
import qualified Language.VHDL.AST as AST

-- GHC API
import CoreSyn
--import qualified Type
import qualified Name
import qualified Var
import qualified IdInfo
import qualified TyCon
import qualified DataCon
--import qualified CoreSubst
import qualified CoreUtils
import Outputable ( showSDoc, ppr )

-- Local imports
import CLasH.Translator.TranslatorTypes
import CLasH.VHDL.VHDLTypes
import CLasH.VHDL.VHDLTools
import CLasH.Utils.Pretty
import CLasH.Utils.Core.CoreTools
import CLasH.VHDL.Constants
import CLasH.VHDL.Generate
import CLasH.VHDL.Testbench

createDesignFiles ::
  [CoreSyn.CoreBndr] -- ^ Top binders
  -> TranslatorSession [(AST.VHDLId, AST.DesignFile)]

createDesignFiles topbndrs = do
  bndrss <- mapM recurseArchitectures topbndrs
  let bndrs = concat bndrss
  lunits <- mapM createLibraryUnit bndrs
  typepackage <- createTypesPackage
  let files = map (Arrow.second $ AST.DesignFile full_context) lunits
  return $ typepackage : files
  where
    full_context =
      mkUseAll ["work", "types"]
      : (mkUseAll ["work"]
      : ieee_context)

ieee_context = [
    AST.Library $ mkVHDLBasicId "IEEE",
    mkUseAll ["IEEE", "std_logic_1164"],
    mkUseAll ["IEEE", "numeric_std"],
    mkUseAll ["std", "textio"]
  ]

-- | Find out which entities are needed for the given top level binders.
recurseArchitectures ::
  CoreSyn.CoreBndr -- ^ The top level binder
  -> TranslatorSession [CoreSyn.CoreBndr] 
  -- ^ The binders of all needed functions.
recurseArchitectures bndr = do
  -- See what this binder directly uses
  (_, used) <- getArchitecture bndr
  -- Recursively check what each of the used functions uses
  useds <- mapM recurseArchitectures used
  -- And return all of them
  return $ bndr : (concat useds)

-- | Creates the types package, based on the current type state.
createTypesPackage ::
  TranslatorSession (AST.VHDLId, AST.DesignFile) 
  -- ^ The id and content of the types package
 
createTypesPackage = do
  tyfuns <- getA (tsType .> tsTypeFuns)
  let tyfun_decls = mkBuiltInShow ++ (map snd $ Map.elems tyfuns)
  ty_decls <- getA (tsType .> tsTypeDecls)
  let subProgSpecs = map (\(AST.SubProgBody spec _ _) -> AST.PDISS spec) tyfun_decls
  let type_package_dec = AST.LUPackageDec $ AST.PackageDec (mkVHDLBasicId "types") ([tfvec_index_decl] ++ ty_decls ++ subProgSpecs)
  let type_package_body = AST.LUPackageBody $ AST.PackageBody typesId tyfun_decls
  return $ (mkVHDLBasicId "types", AST.DesignFile ieee_context [type_package_dec, type_package_body])
  where
    tfvec_index_decl = AST.PDISD $ AST.SubtypeDec tfvec_indexTM tfvec_index_def
    tfvec_range = AST.ConstraintRange $ AST.SubTypeRange (AST.PrimLit "-1") (AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerTM) (AST.NSimple $ highId) Nothing)
    tfvec_index_def = AST.SubtypeIn integerTM (Just tfvec_range)

-- Create a use foo.bar.all statement. Takes a list of components in the used
-- name. Must contain at least two components
mkUseAll :: [String] -> AST.ContextItem
mkUseAll ss = 
  AST.Use $ from AST.:.: AST.All
  where
    base_prefix = (AST.NSimple $ mkVHDLBasicId $ head ss)
    from = foldl select base_prefix (tail ss)
    select prefix s = AST.NSelected $ prefix AST.:.: (AST.SSimple $ mkVHDLBasicId s)
      
createLibraryUnit ::
  CoreSyn.CoreBndr
  -> TranslatorSession (AST.VHDLId, [AST.LibraryUnit])

createLibraryUnit bndr = do
  entity <- getEntity bndr
  (arch, _) <- getArchitecture bndr
  return (ent_id entity, [AST.LUEntity (ent_dec entity), AST.LUArch arch])

{-
-- | Looks up all pairs of old state, new state signals, together with
--   the state id they represent.
makeStatePairs :: FlatFunction -> [(StateId, SignalInfo, SignalInfo)]
makeStatePairs flatfunc =
  [(Maybe.fromJust $ oldStateId $ sigUse old_info, old_info, new_info) 
    | old_info <- map snd (flat_sigs flatfunc)
    , new_info <- map snd (flat_sigs flatfunc)
	-- old_info must be an old state (and, because of the next equality,
	-- new_info must be a new state).
	, Maybe.isJust $ oldStateId $ sigUse old_info
	-- And the state numbers must match
    , (oldStateId $ sigUse old_info) == (newStateId $ sigUse new_info)]

    -- Replace the second tuple element with the corresponding SignalInfo
    --args_states = map (Arrow.second $ signalInfo sigs) args
mkStateProcSm :: (StateId, SignalInfo, SignalInfo) -> AST.ProcSm
mkStateProcSm (num, old, new) =
  AST.ProcSm label [clk] [statement]
  where
    label       = mkVHDLExtId $ "state_" ++ (show num)
    clk         = mkVHDLExtId "clk"
    rising_edge = AST.NSimple $ mkVHDLBasicId "rising_edge"
    wform       = AST.Wform [AST.WformElem (AST.PrimName $ AST.NSimple $ getSignalId new) Nothing]
    assign      = AST.SigAssign (AST.NSimple $ getSignalId old) wform
    rising_edge_clk = AST.PrimFCall $ AST.FCall rising_edge [Nothing AST.:=>: (AST.ADName $ AST.NSimple clk)]
    statement   = AST.IfSm rising_edge_clk [assign] [] Nothing

-- | Creates a VHDL Id from a named SignalInfo. Errors out if the SignalInfo
--   is not named.
getSignalId :: SignalInfo -> AST.VHDLId
getSignalId info =
  mkVHDLExtId $ Maybe.fromMaybe
    (error $ "Unnamed signal? This should not happen!")
    (sigName info)
-}
