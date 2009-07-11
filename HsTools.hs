{-# LANGUAGE ViewPatterns #-}
module HsTools where

-- Standard modules
import qualified Unsafe.Coerce
import qualified Maybe

-- GHC API
import qualified GHC
import qualified HscMain
import qualified HscTypes
import qualified DynFlags
import qualified FastString
import qualified StringBuffer
import qualified MonadUtils
import Outputable ( showSDoc, ppr )
import qualified Outputable
-- Lexer & Parser, i.e. up to HsExpr
import qualified Lexer
import qualified Parser
-- HsExpr representation, renaming, typechecking and desugaring
-- (i.e., everything up to Core).
import qualified HsSyn
import qualified HsExpr
import qualified HsTypes
import qualified HsBinds
import qualified TcRnMonad
import qualified TcRnTypes
import qualified RnExpr
import qualified RnEnv
import qualified TcExpr
import qualified TcEnv
import qualified TcSimplify
import qualified TcTyFuns
import qualified Desugar
import qualified InstEnv
import qualified FamInstEnv
import qualified PrelNames
import qualified Module
import qualified OccName
import qualified RdrName
import qualified Name
import qualified TysWiredIn
import qualified SrcLoc
import qualified LoadIface
import qualified BasicTypes
import qualified Bag
-- Core representation and handling
import qualified CoreSyn
import qualified Id
import qualified Type
import qualified TyCon


-- Local imports
import GhcTools
import CoreShow

-- | Translate a HsExpr to a Core expression. This does renaming, type
-- checking, simplification of class instances and desugaring. The result is
-- a let expression that holds the given expression and a number of binds that
-- are needed for any type classes used to work. For example, the HsExpr:
--  \x = x == (1 :: Int)
-- will result in the CoreExpr
--  let 
--    $dInt = ...
--    (==) = Prelude.(==) Int $dInt 
--  in 
--    \x = (==) x 1
toCore :: 
  [Module.ModuleName] -- ^ The modules that need to be imported before translating
                      --   this expression.
  -> HsSyn.HsExpr RdrName.RdrName -- ^ The expression to translate to Core.
  -> GHC.Ghc CoreSyn.CoreExpr -- ^ The resulting core expression.
toCore modules expr = do
  env <- GHC.getSession
  let icontext = HscTypes.hsc_IC env
  
  (binds, tc_expr) <- HscTypes.ioMsgMaybe $ MonadUtils.liftIO $ 
    -- Translage the TcRn (typecheck-rename) monad into an IO monad
    TcRnMonad.initTcPrintErrors env PrelNames.iNTERACTIVE $ do
      (tc_expr, insts) <- TcRnMonad.getLIE $ do
        mapM importModule modules
        -- Rename the expression, resulting in a HsExpr Name
        (rn_expr, freevars) <- RnExpr.rnExpr expr
        -- Typecheck the expression, resulting in a HsExpr Id and a list of
        -- Insts
        (res, _) <- TcExpr.tcInferRho (SrcLoc.noLoc rn_expr)
        return res
      -- Translate the instances into bindings
      --(insts', binds) <- TcSimplify.tcSimplifyRuleLhs insts
      binds <- TcSimplify.tcSimplifyTop insts
      return (binds, tc_expr)
  
  -- Create a let expression with the extra binds (for polymorphism etc.) and
  -- the resulting expression.
  let letexpr = SrcLoc.noLoc $ HsExpr.HsLet 
        (HsBinds.HsValBinds $ HsBinds.ValBindsOut [(BasicTypes.NonRecursive, binds)] [])
        tc_expr
  -- Desugar the expression, resulting in core.
  let rdr_env  = HscTypes.ic_rn_gbl_env icontext
  desugar_expr <- HscTypes.ioMsgMaybe $ Desugar.deSugarExpr env PrelNames.iNTERACTIVE rdr_env HscTypes.emptyTypeEnv letexpr

  return desugar_expr

-- | Create an Id from a RdrName. Might not work for DataCons...
mkId :: RdrName.RdrName -> GHC.Ghc Id.Id
mkId rdr_name = do
  env <- GHC.getSession
  id <- HscTypes.ioMsgMaybe $ MonadUtils.liftIO $ 
    -- Translage the TcRn (typecheck-rename) monad in an IO monad
    TcRnMonad.initTcPrintErrors env PrelNames.iNTERACTIVE $ 
      -- Automatically import all available modules, so fully qualified names
      -- always work
      TcRnMonad.setOptM DynFlags.Opt_ImplicitImportQualified $ do
        -- Lookup a Name for the RdrName. This finds the package (version) in
        -- which the name resides.
        name <- RnEnv.lookupGlobalOccRn rdr_name
        -- Lookup an Id for the Name. This finds out the the type of the thing
        -- we're looking for.
        --
        -- Note that tcLookupId doesn't seem to work for DataCons. See source for
        -- tcLookupId to find out.
        TcEnv.tcLookupId name 
  return id

normaliseType ::
  HscTypes.HscEnv
  -> Type.Type
  -> IO Type.Type
normaliseType env ty = do
   (err, nty) <- MonadUtils.liftIO $
     -- Initialize the typechecker monad
     TcRnMonad.initTcPrintErrors env PrelNames.iNTERACTIVE $ do
       -- Normalize the type
       (_, nty) <- TcTyFuns.tcNormaliseFamInst ty
       return nty
   let normalized_ty = Maybe.fromJust nty
   return normalized_ty

-- | Translate a core Type to an HsType. Far from complete so far.
coreToHsType :: Type.Type -> HsTypes.LHsType RdrName.RdrName
--  Translate TyConApps
coreToHsType ty = case Type.splitTyConApp_maybe ty of
  Just (tycon, tys) ->
    foldl (\t a -> SrcLoc.noLoc $ HsTypes.HsAppTy t a) tycon_ty (map coreToHsType tys)
    where
      tycon_name = TyCon.tyConName tycon
      mod_name = Module.moduleName $ Name.nameModule tycon_name
      occ_name = Name.nameOccName tycon_name
      tycon_rdrname = RdrName.mkRdrQual mod_name occ_name
      tycon_ty = SrcLoc.noLoc $ HsTypes.HsTyVar tycon_rdrname
  Nothing -> error $ "HsTools.coreToHsType Cannot translate non-tycon type"

-- | Evaluate a CoreExpr and return its value. For this to work, the caller
--   should already know the result type for sure, since the result value is
--   unsafely coerced into this type.
execCore :: CoreSyn.CoreExpr -> GHC.Ghc a
execCore expr = do
        -- Setup session flags (yeah, this seems like a noop, but
        -- setSessionDynFlags really does some extra work...)
        dflags <- GHC.getSessionDynFlags
        GHC.setSessionDynFlags dflags
        -- Compile the expressions. This runs in the IO monad, but really wants
        -- to run an IO-monad-inside-a-GHC-monad for some reason. I don't really
        -- understand what it means, but it works.
        env <- GHC.getSession
        let srcspan = SrcLoc.mkGeneralSrcSpan (FastString.fsLit "XXX")
        hval <- MonadUtils.liftIO $ HscMain.compileExpr env srcspan expr
        let res = Unsafe.Coerce.unsafeCoerce hval :: Int
        return $ Unsafe.Coerce.unsafeCoerce hval

-- These functions build (parts of) a LHSExpr RdrName.

-- | A reference to the Prelude.undefined function.
hsUndef :: HsExpr.LHsExpr RdrName.RdrName
hsUndef = SrcLoc.noLoc $ HsExpr.HsVar PrelNames.undefined_RDR

-- | A typed reference to the Prelude.undefined function.
hsTypedUndef :: HsTypes.LHsType RdrName.RdrName -> HsExpr.LHsExpr RdrName.RdrName
hsTypedUndef ty = SrcLoc.noLoc $ HsExpr.ExprWithTySig hsUndef ty

-- | Create a qualified RdrName from a module name and a variable name
mkRdrName :: String -> String -> RdrName.RdrName
mkRdrName mod var =
    RdrName.mkRdrQual (Module.mkModuleName mod) (OccName.mkVarOcc var)

-- These three functions are simplified copies of those in HscMain, because
-- those functions are not exported. These versions have all error handling
-- removed.
hscParseType = hscParseThing Parser.parseType
hscParseStmt = hscParseThing Parser.parseStmt

hscParseThing :: Lexer.P thing -> DynFlags.DynFlags -> String -> GHC.Ghc thing
hscParseThing parser dflags str = do
    buf <- MonadUtils.liftIO $ StringBuffer.stringToStringBuffer str
    let loc  = SrcLoc.mkSrcLoc (FastString.fsLit "<interactive>") 1 0
    let Lexer.POk _ thing = Lexer.unP parser (Lexer.mkPState buf loc dflags)
    return thing

-- | This function imports the module with the given name, for the renamer /
-- typechecker to use. It also imports any "orphans" and "family instances"
-- from modules included by this module, but not the actual modules
-- themselves. I'm not 100% sure how this works, but it seems that any
-- functions defined in included modules are available just by loading the
-- original module, and by doing this orphan stuff, any (type family or class)
-- instances are available as well.
--
-- Most of the code is based on tcRnImports and rnImportDecl, but those
-- functions do a lot more (which I hope we won't need...).
importModule :: Module.ModuleName -> TcRnTypes.RnM ()
importModule mod = do
  let reason = Outputable.text "Hardcoded import" -- Used for trace output
  let pkg = Nothing
  -- Load the interface.
  iface <- LoadIface.loadSrcInterface reason mod False pkg
  -- Load orphan an familiy instance dependencies as well. I think these
  -- dependencies are needed for the type checker to know all instances. Any
  -- other instances (on other packages) are only useful to the
  -- linker, so we can probably safely ignore them here. Dependencies within
  -- the same package are also listed in deps, but I'm not so sure what to do
  -- with them.
  let deps = HscTypes.mi_deps iface
  let orphs = HscTypes.dep_orphs deps
  let finsts = HscTypes.dep_finsts deps
  LoadIface.loadOrphanModules orphs False
  LoadIface.loadOrphanModules finsts True
