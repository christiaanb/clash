-- 
-- Functions to create a VHDL testbench from a list of test input.
--
module CLasH.VHDL.Testbench where

-- Standard modules
import qualified Control.Monad as Monad
import qualified Maybe
import qualified Data.Map as Map
import qualified Data.Accessor.Monad.Trans.StrictState as MonadState

-- VHDL Imports
import qualified Language.VHDL.AST as AST

-- GHC API
import qualified CoreSyn
import qualified HscTypes
import qualified Var
import qualified TysWiredIn

-- Local imports
import CLasH.Translator.TranslatorTypes
import CLasH.VHDL.Constants
import CLasH.VHDL.Generate
import CLasH.VHDL.VHDLTools
import CLasH.VHDL.VHDLTypes
import CLasH.Normalize
import CLasH.Utils.Core.BinderTools
import CLasH.Utils.Core.CoreTools
import CLasH.Utils

createTestbench :: 
  Maybe Int -- ^ Number of cycles to simulate
  -> [HscTypes.CoreModule] -- ^ Compiled modules
  -> CoreSyn.CoreExpr -- ^ Input stimuli
  -> CoreSyn.CoreBndr -- ^ Top Entity
  -> TranslatorSession CoreSyn.CoreBndr -- ^ The id of the generated archictecture
createTestbench mCycles cores stimuli top = do
  stimuli' <- reduceCoreListToHsList cores stimuli
  -- Create a binder for the testbench. We use the unit type (), since the
  -- testbench has no outputs and no inputs.
  bndr <- mkInternalVar "testbench" TysWiredIn.unitTy
  let entity = createTestbenchEntity bndr
  MonadState.modify tsEntities (Map.insert bndr entity)
  arch <- createTestbenchArch mCycles stimuli' top entity
  MonadState.modify tsArchitectures (Map.insert bndr arch)
  return bndr

createTestbenchEntity :: 
  CoreSyn.CoreBndr
  -> Entity
createTestbenchEntity bndr = entity
  where
    vhdl_id = mkVHDLBasicId "testbench"
    -- Create an AST entity declaration with no ports
    ent_decl = AST.EntityDec vhdl_id []
    -- Create a signature with no input and no output ports
    entity = Entity vhdl_id [] undefined ent_decl

createTestbenchArch ::
  Maybe Int -- ^ Number of cycles to simulate
  -> [CoreSyn.CoreExpr] -- ^ Imput stimuli
  -> CoreSyn.CoreBndr -- ^ Top Entity
  -> Entity -- ^ The signature to create an architecture for
  -> TranslatorSession (Architecture, [CoreSyn.CoreBndr])
  -- ^ The architecture and any other entities used.
createTestbenchArch mCycles stimuli top testent= do
  signature <- getEntity top
  let entId   = ent_id signature
      iIface  = ent_args signature
      oIface  = ent_res signature
      iIds    = map fst iIface
  let (oId, oDec, oProc) = case oIface of
        Just (id, ty) -> ( id
                         , [AST.SigDec id ty Nothing]
                         , [createOutputProc [id]])
        -- No output port? Just use undefined for the output id, since it won't be
        -- used by mkAssocElems when there is no output port.
        Nothing -> (undefined, [], [])
  let iDecs   = map (\(vId, tm) -> AST.SigDec vId tm Nothing) iIface
  let clockId = AST.unsafeVHDLBasicId ("clock1")
  let finalIDecs = iDecs ++
                    [AST.SigDec clockId std_logicTM (Just $ AST.PrimLit "'0'"),
                     AST.SigDec resetId std_logicTM (Just $ AST.PrimLit "'0'")]
  let portmaps = mkAssocElems (map idToVHDLExpr iIds) (AST.NSimple oId) signature
  let mIns    = mkComponentInst "totest" entId [1] portmaps
  (stimuliAssigns, stimuliDecs, cycles, used) <- createStimuliAssigns mCycles stimuli (head iIds)
  let finalAssigns = (AST.CSSASm (AST.NSimple resetId AST.:<==:
                      AST.ConWforms []
                                    (AST.Wform [AST.WformElem (AST.PrimLit "'0'") (Just $ AST.PrimLit "0 ns"), AST.WformElem (AST.PrimLit "'1'") (Just $ AST.PrimLit "3 ns")])
                                    Nothing)) : stimuliAssigns
  let clkProc     = createClkProc
  let arch = AST.ArchBody
              (AST.unsafeVHDLBasicId "test")
              (AST.NSimple $ ent_id testent)
              (map AST.BDISD (finalIDecs ++ stimuliDecs ++ oDec))
              (mIns :
                ( (AST.CSPSm clkProc) : (fmap AST.CSPSm oProc) ++ finalAssigns ) )
  return (arch, top : used)

createStimuliAssigns ::
  Maybe Int -- ^ Number of cycles to simulate
  -> [CoreSyn.CoreExpr] -- ^ Input stimuli
  -> AST.VHDLId -- ^ Input signal
  -> TranslatorSession ( [AST.ConcSm]
                       , [AST.SigDec]
                       , Int
                       , [CoreSyn.CoreBndr]) -- ^ (Resulting statements, Needed signals, The number of cycles to simulate, Any entities used)
createStimuliAssigns mCycles [] _ = return ([], [], Maybe.maybe 0 id mCycles, [])

createStimuliAssigns mCycles stimuli signal = do
  let genWformElem time stim = (AST.WformElem stim (Just $ AST.PrimLit (show time ++ " ns")))
  let inputlen = length stimuli
  assigns <- Monad.zipWithM createStimulans stimuli [0..inputlen]
  let (stimuli_sms, resvars, useds) = unzip3 assigns
  sig_dec_maybes <- mapM mkSigDec resvars
  let sig_decs = Maybe.catMaybes sig_dec_maybes
  outps <- mapM (\x -> MonadState.lift tsType (varToVHDLExpr x)) resvars
  let wformelems = zipWith genWformElem [0,10..] outps
  let inassign = AST.CSSASm $ AST.NSimple signal AST.:<==: AST.ConWforms [] (AST.Wform wformelems) Nothing
  case (concat stimuli_sms) of
    []        -> return ([inassign], [], inputlen, concat useds)
    stims     -> return (stims ++ [inassign], sig_decs, inputlen, concat useds)

createStimulans ::
  CoreSyn.CoreExpr -- ^ The stimulans
  -> Int -- ^ The cycle for this stimulans
  -> TranslatorSession ( [AST.ConcSm]
                       , Var.Var 
                       , [CoreSyn.CoreBndr]) -- ^ (The statement, the variable it assigns to (assumed to be available!), Any entities used by this stimulans)

createStimulans expr cycl = do 
  -- There must be a let at top level 
  expr <- normalizeExpr ("test input #" ++ show cycl) transforms expr
  -- Split the normalized expression. It can't have a function type, so match
  -- an empty list of argument binders
  let ([], binds, res) = splitNormalized expr
  (stimulansbindss, useds) <- unzipM $ Monad.mapM mkConcSm binds
  sig_dec_maybes <- mapM (mkSigDec . fst) (filter ((/=res).fst) binds)
  let sig_decs = map (AST.BDISD) (Maybe.catMaybes sig_dec_maybes)
  let block_label = mkVHDLExtId ("testcycle_" ++ (show cycl))
  let block = AST.BlockSm block_label [] (AST.PMapAspect []) sig_decs (concat stimulansbindss)
  case (sig_decs,(concat stimulansbindss)) of
    ([],[])   ->  return ([], res, concat useds)
    otherwise ->  return ([AST.CSBSm block], res, concat useds)
 
-- | generates a clock process with a period of 10ns
createClkProc :: AST.ProcSm
createClkProc = AST.ProcSm (AST.unsafeVHDLBasicId "clkproc") [] sms
 where clockId = AST.unsafeVHDLBasicId ("clock1")
       sms = -- wait for 5 ns -- (half a cycle)
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
 where clockId = AST.unsafeVHDLBasicId ("clock1")
       clkPred = AST.PrimName (AST.NAttribute $ AST.AttribName (AST.NSimple clockId) 
                                                   (AST.NSimple eventId)
                                                   Nothing          ) `AST.And` 
                 (AST.PrimName (AST.NSimple clockId) AST.:=: AST.PrimLit "'1'")
       writeOuts :: [AST.VHDLId] -> [AST.SeqSm]
       writeOuts []  = []
       writeOuts [i] = [writeOut i (AST.PrimLit "LF")]
       writeOuts (i:is) = writeOut i (AST.PrimLit "HT") : writeOuts is
       writeOut outSig suffix = 
         genExprPCall2 writeId
                        (AST.PrimName $ AST.NSimple outputId)
                        ((genExprFCall2 showId (AST.PrimName $ AST.NSimple outSig, AST.PrimLit "false")) AST.:&: suffix)
