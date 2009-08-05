-- 
-- Functions to create a VHDL testbench from a list of test input.
--
module CLasH.VHDL.Testbench where

-- Standard modules
import qualified Control.Monad as Monad
import qualified Maybe
import qualified Data.Map as Map
import Data.Accessor
import qualified Data.Accessor.MonadState as MonadState

-- ForSyDe
import qualified Language.VHDL.AST as AST

-- GHC API
import CoreSyn
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
  -> CoreSyn.CoreExpr -- ^ Input stimuli
  -> CoreSyn.CoreBndr -- ^ Top Entity
  -> TranslatorSession CoreBndr -- ^ The id of the generated archictecture
createTestbench mCycles stimuli top = do
  let stimuli' = reduceCoreListToHsList stimuli
  -- Create a binder for the testbench. We use the unit type (), since the
  -- testbench has no outputs and no inputs.
  bndr <- mkInternalVar "testbench" TysWiredIn.unitTy
  let entity = createTestbenchEntity bndr
  modA tsEntities (Map.insert bndr entity)
  arch <- createTestbenchArch mCycles stimuli' top
  modA tsArchitectures (Map.insert bndr arch)
  return bndr

createTestbenchEntity :: 
  CoreSyn.CoreBndr
  -> Entity
createTestbenchEntity bndr = entity
  where
    vhdl_id = mkVHDLBasicId $ varToString bndr
    -- Create an AST entity declaration with no ports
    ent_decl = AST.EntityDec vhdl_id []
    -- Create a signature with no input and no output ports
    entity = Entity vhdl_id [] undefined ent_decl

createTestbenchArch ::
  Maybe Int -- ^ Number of cycles to simulate
  -> [CoreSyn.CoreExpr] -- ^ Imput stimuli
  -> CoreSyn.CoreBndr -- ^ Top Entity
  -> TranslatorSession (Architecture, [CoreSyn.CoreBndr])
  -- ^ The architecture and any other entities used.
createTestbenchArch mCycles stimuli top = do
  signature <- getEntity top
  let entId   = ent_id signature
      iIface  = ent_args signature
      oIface  = ent_res signature
      iIds    = map fst iIface
      oId     = fst oIface
  let iDecs   = map (\(vId, tm) -> AST.SigDec vId tm Nothing) iIface
  let finalIDecs = iDecs ++
                    [AST.SigDec clockId std_logicTM (Just $ AST.PrimLit "'0'"),
                     AST.SigDec resetId std_logicTM (Just $ AST.PrimLit "'0'")]
  let oDecs   = AST.SigDec (fst oIface) (snd oIface) Nothing
  let portmaps = mkAssocElems (map idToVHDLExpr iIds) (AST.NSimple oId) signature
  let mIns    = mkComponentInst "totest" entId portmaps
  (stimuliAssigns, stimuliDecs, cycles, used) <- createStimuliAssigns mCycles stimuli (head iIds)
  let finalAssigns = (AST.CSSASm (AST.NSimple resetId AST.:<==:
                      AST.ConWforms []
                                    (AST.Wform [AST.WformElem (AST.PrimLit "'1'") (Just $ AST.PrimLit "3 ns")])
                                    Nothing)) : stimuliAssigns
  let clkProc     = createClkProc
  let outputProc  = createOutputProc [oId]
  let arch = AST.ArchBody
              (AST.unsafeVHDLBasicId "test")
              (AST.NSimple $ AST.unsafeIdAppend entId "_tb")
              (map AST.BDISD (finalIDecs ++ stimuliDecs ++ [oDecs]))
              (mIns :
                ( (AST.CSPSm clkProc) : (AST.CSPSm outputProc) : finalAssigns ) )
  return (arch, top : used)

createStimuliAssigns ::
  Maybe Int -- ^ Number of cycles to simulate
  -> [CoreSyn.CoreExpr] -- ^ Input stimuli
  -> AST.VHDLId -- ^ Input signal
  -> TranslatorSession ( [AST.ConcSm] -- ^ Resulting statemetns
                       , [AST.SigDec] -- ^ Needed signals
                       , Int -- ^ The number of cycles to simulate
                       , [CoreSyn.CoreBndr]) -- ^ Any entities used
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
  return (stimuli_sms ++ [inassign], sig_decs, inputlen, concat useds)

createStimulans ::
  CoreSyn.CoreExpr -- ^ The stimulans
  -> Int -- ^ The cycle for this stimulans
  -> TranslatorSession ( AST.ConcSm -- ^ The statement
                       , Var.Var -- ^ the variable it assigns to (assumed to be available!)
                       , [CoreSyn.CoreBndr]) -- ^ Any entities used by this stimulans

createStimulans expr cycl = do 
  -- There must be a let at top level 
  (CoreSyn.Let (CoreSyn.Rec binds) (Var res)) <- normalizeExpr ("test input #" ++ show cycl) expr
  (stimulansbindss, useds) <- unzipM $ Monad.mapM mkConcSm binds
  sig_dec_maybes <- mapM (mkSigDec . fst) (filter ((/=res).fst) binds)
  let sig_decs = map (AST.BDISD) (Maybe.catMaybes $ sig_dec_maybes)
  let block_label = mkVHDLExtId ("testcycle_" ++ (show cycl))
  let block = AST.BlockSm block_label [] (AST.PMapAspect []) sig_decs (concat stimulansbindss)  
  return (AST.CSBSm block, res, concat useds)
 
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
