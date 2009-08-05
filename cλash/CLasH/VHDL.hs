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
-- import CLasH.VHDL.Testbench

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

{-
createTestBench :: 
  Maybe Int -- ^ Number of cycles to simulate
  -> [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)] -- ^ Input stimuli
  -> CoreSyn.CoreBndr -- ^ Top Entity
  -> VHDLSession (AST.VHDLId, [AST.LibraryUnit]) -- ^ Testbench
createTestBench mCycles stimuli topEntity = do
  ent@(AST.EntityDec id _) <- createTestBenchEntity topEntity
  arch <- createTestBenchArch mCycles stimuli topEntity
  return (id, [AST.LUEntity ent, AST.LUArch arch])
  

createTestBenchEntity ::
  CoreSyn.CoreBndr -- ^ Top Entity
  -> VHDLSession AST.EntityDec -- ^ TB Entity
createTestBenchEntity topEntity = do
  signaturemap <- getA vsSignatures
  let signature = Maybe.fromMaybe 
        (error $ "\nTestbench.createTestBenchEntity: Generating testbench for function \n" ++ (pprString topEntity) ++ "\nwithout signature? This should not happen!")
        (Map.lookup topEntity signaturemap)
  let signaturename = ent_id signature
  return $ AST.EntityDec (AST.unsafeIdAppend signaturename "_tb") []
  
createTestBenchArch ::
  Maybe Int -- ^ Number of cycles to simulate
  -> [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)] -- ^ Imput stimulie
  -> CoreSyn.CoreBndr -- ^ Top Entity
  -> VHDLSession AST.ArchBody
createTestBenchArch mCycles stimuli topEntity = do
  signaturemap <- getA vsSignatures
  let signature = Maybe.fromMaybe 
        (error $ "\nTestbench.createTestBenchArch: Generating testbench for function \n" ++ (pprString topEntity) ++ "\nwithout signature? This should not happen!")
        (Map.lookup topEntity signaturemap)
  let entId   = ent_id signature
      iIface  = ent_args signature
      oIface  = ent_res signature
      iIds    = map fst iIface
      oIds    = fst oIface
  let iDecs   = map (\(vId, tm) -> AST.SigDec vId tm Nothing) iIface
  let finalIDecs = iDecs ++
                    [AST.SigDec clockId std_logicTM (Just $ AST.PrimLit "'0'"),
                     AST.SigDec resetId std_logicTM (Just $ AST.PrimLit "'0'")]
  let oDecs   = AST.SigDec (fst oIface) (snd oIface) Nothing
  let portmaps = mkAssocElems (map idToVHDLExpr iIds) (AST.NSimple oIds) signature
  let mIns    = mkComponentInst "totest" entId portmaps
  (stimuliAssigns, stimuliDecs, cycles) <- createStimuliAssigns mCycles stimuli (head iIds)
  let finalAssigns = (AST.CSSASm (AST.NSimple resetId AST.:<==:
                      AST.ConWforms []
                                    (AST.Wform [AST.WformElem (AST.PrimLit "'1'") (Just $ AST.PrimLit "3 ns")])
                                    Nothing)) : stimuliAssigns
  let clkProc     = createClkProc
  let outputProc  = createOutputProc [oIds]
  return $ (AST.ArchBody
              (AST.unsafeVHDLBasicId "test")
              (AST.NSimple $ AST.unsafeIdAppend entId "_tb")
              (map AST.BDISD (finalIDecs ++ stimuliDecs ++ [oDecs]))
              (mIns :
                ( (AST.CSPSm clkProc) : (AST.CSPSm outputProc) : finalAssigns ) ) )

createStimuliAssigns ::
  Maybe Int -- ^ Number of cycles to simulate
  -> [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)] -- ^ Input stimuli
  -> AST.VHDLId -- ^ Input signal
  -> VHDLSession ([AST.ConcSm], [AST.SigDec], Int)
createStimuliAssigns mCycles [] _ = return ([], [], Maybe.maybe 0 id mCycles)

createStimuliAssigns mCycles stimuli signal = do
  let genWformElem time stim = (AST.WformElem stim (Just $ AST.PrimLit (show time ++ " ns")))
  let inputlen = length stimuli
  assigns <- Monad.zipWithM createStimulans stimuli [0..inputlen]
  let resvars = (map snd assigns)
  sig_dec_maybes <- mapM mkSigDec resvars
  let sig_decs = Maybe.catMaybes sig_dec_maybes
  outps <- mapM (\x -> MonadState.lift vsType (varToVHDLExpr x)) resvars
  let wformelems = zipWith genWformElem [0,10..] outps
  let inassign = AST.CSSASm $ AST.NSimple signal AST.:<==: AST.ConWforms [] (AST.Wform wformelems) Nothing
  return ((map fst assigns) ++ [inassign], sig_decs, inputlen)

createStimulans :: (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -> Int -> VHDLSession (AST.ConcSm, Var.Var)
createStimulans (bndr, expr) cycl = do 
  -- There must be a let at top level 
  let (CoreSyn.Let (CoreSyn.Rec binds) (Var res)) = expr
  stimulansbinds <- Monad.mapM mkConcSm binds
  sig_dec_maybes <- mapM (mkSigDec . fst) (filter ((/=res).fst) binds)
  let sig_decs = map (AST.BDISD) (Maybe.catMaybes $ sig_dec_maybes)
  let block_label = mkVHDLExtId ("testcycle_" ++ (show cycl))
  let block = AST.BlockSm block_label [] (AST.PMapAspect []) sig_decs (concat stimulansbinds)  
  return (AST.CSBSm block, res)
 
-- | generates a clock process with a period of 10ns
createClkProc :: AST.ProcSm
createClkProc = AST.ProcSm (AST.unsafeVHDLBasicId "clkproc") [] sms
 where sms = -- wait for 5 ns -- (half a cycle)
             [AST.WaitFor $ AST.PrimLit "5 ns",
              -- clk <= not clk;
              AST.NSimple clockId `AST.SigAssign` 
                 AST.Wform [AST.WformElem (AST.Not (AST.PrimName $ AST.NSimple clockId)) Nothing]]

-- | generate the output process
createOutputProc :: [AST.VHDLId] -- ^ output signal
              -> AST.ProcSm  
createOutputProc outs = 
  AST.ProcSm (AST.unsafeVHDLBasicId "writeoutput") 
         [clockId]
         [AST.IfSm clkPred (writeOuts outs) [] Nothing]
 where clkPred = AST.PrimName (AST.NAttribute $ AST.AttribName (AST.NSimple clockId) 
                                                   (AST.NSimple $ eventId)
                                                   Nothing          ) `AST.And` 
                 (AST.PrimName (AST.NSimple clockId) AST.:=: AST.PrimLit "'1'")
       writeOuts :: [AST.VHDLId] -> [AST.SeqSm]
       writeOuts []  = []
       writeOuts [i] = [writeOut i (AST.PrimLit "LF")]
       writeOuts (i:is) = writeOut i (AST.PrimLit "HT") : writeOuts is
       writeOut outSig suffix = 
         genExprPCall2 writeId
                        (AST.PrimName $ AST.NSimple outputId)
                        ((genExprFCall showId (AST.PrimName $ AST.NSimple outSig)) AST.:&: suffix)

-}
