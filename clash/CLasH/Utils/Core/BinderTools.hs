--
-- This module contains functions that manipulate binders in various ways.
--
module CLasH.Utils.Core.BinderTools where

-- Standard modules
import qualified Data.Accessor.Monad.Trans.StrictState as MonadState

-- GHC API
import qualified CoreSyn
import qualified Type
import qualified UniqSupply
import qualified Unique
import qualified OccName
import qualified Name
import qualified Module
import qualified Var
import qualified SrcLoc
import qualified IdInfo
import qualified CoreUtils

-- Local imports
import CLasH.Translator.TranslatorTypes

-- Create a new Unique
mkUnique :: TranslatorSession Unique.Unique    
mkUnique = do
  us <- MonadState.get tsUniqSupply 
  let (us', us'') = UniqSupply.splitUniqSupply us
  MonadState.set tsUniqSupply us'
  return $ UniqSupply.uniqFromSupply us''

-- Create a new internal var with the given name and type. A Unique is
-- appended to the given name, to ensure uniqueness (not strictly neccesary,
-- since the Unique is also stored in the name, but this ensures variable
-- names are unique in the output).
mkInternalVar :: String -> Type.Type -> TranslatorSession Var.Var
mkInternalVar str ty = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc str
  let name = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkLocalVar IdInfo.VanillaId name ty IdInfo.vanillaIdInfo

-- Create a new type variable with the given name and kind. A Unique is
-- appended to the given name, to ensure uniqueness (not strictly neccesary,
-- since the Unique is also stored in the name, but this ensures variable
-- names are unique in the output).
mkTypeVar :: String -> Type.Kind -> TranslatorSession Var.Var
mkTypeVar str kind = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc str
  let name = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkTyVar name kind

-- Creates a binder for the given expression with the given name. This
-- works for both value and type level expressions, so it can return a Var or
-- TyVar (which is just an alias for Var).
mkBinderFor :: CoreSyn.CoreExpr -> String -> TranslatorSession Var.Var
mkBinderFor (CoreSyn.Type ty) string = mkTypeVar string (Type.typeKind ty)
mkBinderFor expr string = mkInternalVar string (CoreUtils.exprType expr)

-- Creates a reference to the given variable. This works for both a normal
-- variable as well as a type variable
mkReferenceTo :: Var.Var -> CoreSyn.CoreExpr
mkReferenceTo var | Var.isTyVar var = (CoreSyn.Type $ Type.mkTyVarTy var)
                  | otherwise       = (CoreSyn.Var var)

cloneVar :: Var.Var -> TranslatorSession Var.Var
cloneVar v = do
  uniq <- mkUnique
  -- Swap out the unique, and reset the IdInfo (I'm not 100% sure what it
  -- contains, but vannillaIdInfo is always correct, since it means "no info").
  return $ Var.lazySetIdInfo (Var.setVarUnique v uniq) IdInfo.vanillaIdInfo

-- Creates a new function with the same name as the given binder (but with a
-- new unique) and with the given function body. Returns the new binder for
-- this function.
mkFunction :: CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> TranslatorSession CoreSyn.CoreBndr
mkFunction bndr body = do
  let ty = CoreUtils.exprType body
  id <- cloneVar bndr
  let newid = Var.setVarType id ty
  addGlobalBind newid body
  return newid

-- Returns the full name of a NamedThing, in the forum
-- modulename.occname
getFullString :: Name.NamedThing a => a -> String
getFullString thing = modstr ++ occstr
  where
    name    = Name.getName thing
    modstr  = case Name.nameModule_maybe name of
      Nothing -> ""
      Just mod -> Module.moduleNameString (Module.moduleName mod) ++ "."
    occstr  = Name.getOccString name
