--
-- Functions to generate VHDL from FlatFunctions
--
module CLasH.VHDL where

-- Standard modules
import qualified Data.Map as Map
import qualified Maybe
import qualified Control.Arrow as Arrow
import Data.Accessor
import qualified Data.Accessor.Monad.Trans.StrictState as MonadState

-- VHDL Imports
import qualified Language.VHDL.AST as AST

-- GHC API
import qualified CoreSyn

-- Local imports
import CLasH.Translator.TranslatorTypes
import CLasH.VHDL.VHDLTypes
import CLasH.VHDL.VHDLTools
import CLasH.VHDL.Constants
import CLasH.VHDL.Generate

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
  tyfuns <- MonadState.get (tsType .> tsTypeFuns)
  let tyfun_decls = mkBuiltInShow ++ map snd (Map.elems tyfuns)
  ty_decls_maybes <- MonadState.get (tsType .> tsTypeDecls)
  let ty_decls = Maybe.catMaybes ty_decls_maybes
  let subProgSpecs = map (\(AST.SubProgBody spec _ _) -> AST.PDISS spec) tyfun_decls
  let type_package_dec = AST.LUPackageDec $ AST.PackageDec (mkVHDLBasicId "types") ([tfvec_index_decl] ++ ty_decls ++ subProgSpecs)
  let type_package_body = AST.LUPackageBody $ AST.PackageBody typesId tyfun_decls
  return (mkVHDLBasicId "types", AST.DesignFile ieee_context [type_package_dec, type_package_body])
  where
    tfvec_index_decl = AST.PDISD $ AST.SubtypeDec tfvec_indexTM tfvec_index_def
    tfvec_range = AST.ConstraintRange $ AST.SubTypeRange (AST.PrimLit "-1") (AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerTM) (AST.NSimple highId) Nothing)
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
