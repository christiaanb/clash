--
-- Functions to generate VHDL from FlatFunctions
--
module CLasH.VHDL where

-- Standard modules
import qualified Data.List as List
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
import qualified Id
import qualified IdInfo
import qualified TyCon
import qualified DataCon
--import qualified CoreSubst
import qualified CoreUtils
import Outputable ( showSDoc, ppr )

-- Local imports
import CLasH.VHDL.VHDLTypes
import CLasH.VHDL.VHDLTools
import CLasH.Utils.Pretty
import CLasH.Utils.Core.CoreTools
import CLasH.VHDL.Constants
import CLasH.VHDL.Generate
-- import CLasH.VHDL.Testbench

createDesignFiles ::
  TypeState
  -> [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
  -> CoreSyn.CoreBndr -- ^ Top binder
  -> [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)] -- ^ Test Input
  -> [(AST.VHDLId, AST.DesignFile)]

createDesignFiles init_typestate binds topbind testinput =
  (mkVHDLBasicId "types", AST.DesignFile ieee_context [type_package_dec, type_package_body]) :
  map (Arrow.second $ AST.DesignFile full_context) (units ++ [testbench])
  
  where
    init_session = VHDLState init_typestate Map.empty
    (units, final_session') = 
      State.runState (createLibraryUnits binds) init_session
    (testbench, final_session) =
      State.runState (createTestBench Nothing testinput topbind) final_session'
    tyfun_decls = mkBuiltInShow ++ (map snd $ Map.elems (final_session ^. vsType ^. vsTypeFuns))
    ty_decls = final_session ^. vsType ^. vsTypeDecls
    tfvec_index_decl = AST.PDISD $ AST.SubtypeDec tfvec_indexTM tfvec_index_def
    tfvec_range = AST.ConstraintRange $ AST.SubTypeRange (AST.PrimLit "-1") (AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerTM) (AST.NSimple $ highId) Nothing)
    tfvec_index_def = AST.SubtypeIn integerTM (Just tfvec_range)
    ieee_context = [
        AST.Library $ mkVHDLBasicId "IEEE",
        mkUseAll ["IEEE", "std_logic_1164"],
        mkUseAll ["IEEE", "numeric_std"],
        mkUseAll ["std", "textio"]
      ]
    full_context =
      mkUseAll ["work", "types"]
      : (mkUseAll ["work"]
      : ieee_context)
    type_package_dec = AST.LUPackageDec $ AST.PackageDec (mkVHDLBasicId "types") ([tfvec_index_decl] ++ ty_decls ++ subProgSpecs)
    type_package_body = AST.LUPackageBody $ AST.PackageBody typesId tyfun_decls
    subProgSpecs = map subProgSpec tyfun_decls
    subProgSpec = \(AST.SubProgBody spec _ _) -> AST.PDISS spec

-- Create a use foo.bar.all statement. Takes a list of components in the used
-- name. Must contain at least two components
mkUseAll :: [String] -> AST.ContextItem
mkUseAll ss = 
  AST.Use $ from AST.:.: AST.All
  where
    base_prefix = (AST.NSimple $ mkVHDLBasicId $ head ss)
    from = foldl select base_prefix (tail ss)
    select prefix s = AST.NSelected $ prefix AST.:.: (AST.SSimple $ mkVHDLBasicId s)
      
createLibraryUnits ::
  [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
  -> VHDLSession [(AST.VHDLId, [AST.LibraryUnit])]

createLibraryUnits binds = do
  entities <- Monad.mapM createEntity binds
  archs <- Monad.mapM createArchitecture binds
  return $ zipWith 
    (\ent arch -> 
      let AST.EntityDec id _ = ent in 
      (id, [AST.LUEntity ent, AST.LUArch arch])
    )
    entities archs

-- | Create an entity for a given function
createEntity ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The function
  -> VHDLSession AST.EntityDec -- ^ The resulting entity

createEntity (fname, expr) = do
      -- Strip off lambda's, these will be arguments
      let (args, letexpr) = CoreSyn.collectBinders expr
      args' <- Monad.mapM mkMap args
      -- There must be a let at top level 
      let (CoreSyn.Let binds (CoreSyn.Var res)) = letexpr
      res' <- mkMap res
      let vhdl_id = mkVHDLBasicId $ varToString fname ++ "_" ++ varToStringUniq fname
      let ent_decl' = createEntityAST vhdl_id args' res'
      let AST.EntityDec entity_id _ = ent_decl' 
      let signature = Entity entity_id args' res'
      modA vsSignatures (Map.insert fname signature)
      return ent_decl'
  where
    mkMap ::
      --[(SignalId, SignalInfo)] 
      CoreSyn.CoreBndr 
      -> VHDLSession Port
    -- We only need the vsTypes element from the state
    mkMap = (\bndr ->
      let
        --info = Maybe.fromMaybe
        --  (error $ "Signal not found in the name map? This should not happen!")
        --  (lookup id sigmap)
        --  Assume the bndr has a valid VHDL id already
        id = varToVHDLId bndr
        ty = Var.varType bndr
        error_msg = "\nVHDL.createEntity.mkMap: Can not create entity: " ++ pprString fname ++ "\nbecause no type can be created for port: " ++ pprString bndr 
      in do
        type_mark <- MonadState.lift vsType $ vhdl_ty error_msg ty
        return (id, type_mark)
     )

-- | Create the VHDL AST for an entity
createEntityAST ::
  AST.VHDLId                   -- ^ The name of the function
  -> [Port]                    -- ^ The entity's arguments
  -> Port                      -- ^ The entity's result
  -> AST.EntityDec             -- ^ The entity with the ent_decl filled in as well

createEntityAST vhdl_id args res =
  AST.EntityDec vhdl_id ports
  where
    -- Create a basic Id, since VHDL doesn't grok filenames with extended Ids.
    ports = map (mkIfaceSigDec AST.In) args
              ++ [mkIfaceSigDec AST.Out res]
              ++ [clk_port]
    -- Add a clk port if we have state
    clk_port = AST.IfaceSigDec clockId AST.In std_logicTM

-- | Create a port declaration
mkIfaceSigDec ::
  AST.Mode                         -- ^ The mode for the port (In / Out)
  -> (AST.VHDLId, AST.TypeMark)    -- ^ The id and type for the port
  -> AST.IfaceSigDec               -- ^ The resulting port declaration

mkIfaceSigDec mode (id, ty) = AST.IfaceSigDec id mode ty

{-
-- | Generate a VHDL entity name for the given hsfunc
mkEntityId hsfunc =
  -- TODO: This doesn't work for functions with multiple signatures!
  -- Use a Basic Id, since using extended id's for entities throws off
  -- precision and causes problems when generating filenames.
  mkVHDLBasicId $ hsFuncName hsfunc
-}

-- | Create an architecture for a given function
createArchitecture ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The function
  -> VHDLSession AST.ArchBody -- ^ The architecture for this function

createArchitecture (fname, expr) = do
  signaturemap <- getA vsSignatures
  let signature = Maybe.fromMaybe 
        (error $ "\nVHDL.createArchitecture: Generating architecture for function \n" ++ (pprString fname) ++ "\nwithout signature? This should not happen!")
        (Map.lookup fname signaturemap)
  let entity_id = ent_id signature
  -- Strip off lambda's, these will be arguments
  let (args, letexpr) = CoreSyn.collectBinders expr
  -- There must be a let at top level 
  let (CoreSyn.Let (CoreSyn.Rec binds) (Var res)) = letexpr

  -- Create signal declarations for all binders in the let expression, except
  -- for the output port (that will already have an output port declared in
  -- the entity).
  sig_dec_maybes <- mapM (mkSigDec' . fst) (filter ((/=res).fst) binds)
  let sig_decs = Maybe.catMaybes $ sig_dec_maybes

  statementss <- Monad.mapM mkConcSm binds
  let statements = concat statementss
  return $ AST.ArchBody (mkVHDLBasicId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) (statements ++ procs')
  where
    procs = [] --map mkStateProcSm [] -- (makeStatePairs flatfunc)
    procs' = map AST.CSPSm procs
    -- mkSigDec only uses vsTypes from the state
    mkSigDec' = mkSigDec

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

-- | Transforms a core binding into a VHDL concurrent statement
mkConcSm ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The binding to process
  -> VHDLSession [AST.ConcSm] -- ^ The corresponding VHDL component instantiations.


-- Ignore Cast expressions, they should not longer have any meaning as long as
-- the type works out.
mkConcSm (bndr, Cast expr ty) = mkConcSm (bndr, expr)

-- Simple a = b assignments are just like applications, but without arguments.
-- We can't just generate an unconditional assignment here, since b might be a
-- top level binding (e.g., a function with no arguments).
mkConcSm (bndr, Var v) = do
  genApplication (Left bndr) v []

mkConcSm (bndr, app@(CoreSyn.App _ _))= do
  let (CoreSyn.Var f, args) = CoreSyn.collectArgs app
  let valargs = get_val_args (Var.varType f) args
  genApplication (Left bndr) f (map Left valargs)

-- A single alt case must be a selector. This means thee scrutinee is a simple
-- variable, the alternative is a dataalt with a single non-wild binder that
-- is also returned.
mkConcSm (bndr, expr@(Case (Var scrut) b ty [alt])) =
  case alt of
    (DataAlt dc, bndrs, (Var sel_bndr)) -> do
      case List.elemIndex sel_bndr bndrs of
        Just i -> do
          labels <- MonadState.lift vsType $ getFieldLabels (Id.idType scrut)
          let label = labels!!i
          let sel_name = mkSelectedName (varToVHDLName scrut) label
          let sel_expr = AST.PrimName sel_name
          return [mkUncondAssign (Left bndr) sel_expr]
        Nothing -> error $ "\nVHDL.mkConcSM: Not in normal form: Not a selector case:\n" ++ (pprString expr)
      
    _ -> error $ "\nVHDL.mkConcSM: Not in normal form: Not a selector case:\n" ++ (pprString expr)

-- Multiple case alt are be conditional assignments and have only wild
-- binders in the alts and only variables in the case values and a variable
-- for a scrutinee. We check the constructor of the second alt, since the
-- first is the default case, if there is any.
mkConcSm (bndr, (Case (Var scrut) b ty [(_, _, Var false), (con, _, Var true)])) = do
  scrut' <- MonadState.lift vsType $ varToVHDLExpr scrut
  let cond_expr = scrut' AST.:=: (altconToVHDLExpr con)
  true_expr <- MonadState.lift vsType $ varToVHDLExpr true
  false_expr <- MonadState.lift vsType $ varToVHDLExpr false
  return [mkCondAssign (Left bndr) cond_expr true_expr false_expr]

mkConcSm (_, (Case (Var _) _ _ alts)) = error "\nVHDL.mkConcSm: Not in normal form: Case statement with more than two alternatives"
mkConcSm (_, Case _ _ _ _) = error "\nVHDL.mkConcSm: Not in normal form: Case statement has does not have a simple variable as scrutinee"
mkConcSm (bndr, expr) = error $ "\nVHDL.mkConcSM: Unsupported binding in let expression: " ++ pprString bndr ++ " = " ++ pprString expr


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
