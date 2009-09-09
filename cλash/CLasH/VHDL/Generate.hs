module CLasH.VHDL.Generate where

-- Standard modules
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Maybe
import qualified Data.Either as Either
import Data.Accessor
import Data.Accessor.MonadState as MonadState
import Debug.Trace

-- ForSyDe
import qualified Language.VHDL.AST as AST

-- GHC API
import qualified CoreSyn
import qualified Type
import qualified Var
import qualified Id
import qualified IdInfo
import qualified Literal
import qualified Name
import qualified TyCon

-- Local imports
import CLasH.Translator.TranslatorTypes
import CLasH.VHDL.Constants
import CLasH.VHDL.VHDLTypes
import CLasH.VHDL.VHDLTools
import CLasH.Utils as Utils
import CLasH.Utils.Core.CoreTools
import CLasH.Utils.Pretty
import qualified CLasH.Normalize as Normalize

-----------------------------------------------------------------------------
-- Functions to generate VHDL for user-defined functions.
-----------------------------------------------------------------------------

-- | Create an entity for a given function
getEntity ::
  CoreSyn.CoreBndr
  -> TranslatorSession Entity -- ^ The resulting entity

getEntity fname = Utils.makeCached fname tsEntities $ do
      expr <- Normalize.getNormalized fname
      -- Split the normalized expression
      let (args, binds, res) = Normalize.splitNormalized expr
      -- Generate ports for all non-empty types
      args' <- catMaybesM $ mapM mkMap args
      -- TODO: Handle Nothing
      res' <- mkMap res
      count <- getA tsEntityCounter 
      let vhdl_id = mkVHDLBasicId $ varToString fname ++ "Component_" ++ show count
      putA tsEntityCounter (count + 1)
      let ent_decl = createEntityAST vhdl_id args' res'
      let signature = Entity vhdl_id args' res' ent_decl
      return signature
  where
    mkMap ::
      --[(SignalId, SignalInfo)] 
      CoreSyn.CoreBndr 
      -> TranslatorSession (Maybe Port)
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
        type_mark_maybe <- MonadState.lift tsType $ vhdl_ty error_msg ty
        case type_mark_maybe of 
          Just type_mark -> return $ Just (id, type_mark)
          Nothing -> return Nothing
     )

-- | Create the VHDL AST for an entity
createEntityAST ::
  AST.VHDLId                   -- ^ The name of the function
  -> [Port]                    -- ^ The entity's arguments
  -> Maybe Port                -- ^ The entity's result
  -> AST.EntityDec             -- ^ The entity with the ent_decl filled in as well

createEntityAST vhdl_id args res =
  AST.EntityDec vhdl_id ports
  where
    -- Create a basic Id, since VHDL doesn't grok filenames with extended Ids.
    ports = map (mkIfaceSigDec AST.In) args
              ++ (Maybe.maybeToList res_port)
              ++ [clk_port,resetn_port]
    -- Add a clk port if we have state
    clk_port = AST.IfaceSigDec clockId AST.In std_logicTM
    resetn_port = AST.IfaceSigDec resetId AST.In std_logicTM
    res_port = fmap (mkIfaceSigDec AST.Out) res

-- | Create a port declaration
mkIfaceSigDec ::
  AST.Mode                         -- ^ The mode for the port (In / Out)
  -> Port                          -- ^ The id and type for the port
  -> AST.IfaceSigDec               -- ^ The resulting port declaration

mkIfaceSigDec mode (id, ty) = AST.IfaceSigDec id mode ty

-- | Create an architecture for a given function
getArchitecture ::
  CoreSyn.CoreBndr -- ^ The function to get an architecture for
  -> TranslatorSession (Architecture, [CoreSyn.CoreBndr])
  -- ^ The architecture for this function

getArchitecture fname = Utils.makeCached fname tsArchitectures $ do
  expr <- Normalize.getNormalized fname
  -- Split the normalized expression
  let (args, binds, res) = Normalize.splitNormalized expr
  
  -- Get the entity for this function
  signature <- getEntity fname
  let entity_id = ent_id signature

  -- Create signal declarations for all binders in the let expression, except
  -- for the output port (that will already have an output port declared in
  -- the entity).
  sig_dec_maybes <- mapM (mkSigDec . fst) (filter ((/=res).fst) binds)
  let sig_decs = Maybe.catMaybes $ sig_dec_maybes
  -- Process each bind, resulting in info about state variables and concurrent
  -- statements.
  (state_vars, sms) <- Monad.mapAndUnzipM dobind binds
  let (in_state_maybes, out_state_maybes) = unzip state_vars
  let (statementss, used_entitiess) = unzip sms
  -- Create a state proc, if needed
  state_proc <- case (Maybe.catMaybes in_state_maybes, Maybe.catMaybes out_state_maybes) of
        ([in_state], [out_state]) -> mkStateProcSm (in_state, out_state)
        ([], []) -> return []
        (ins, outs) -> error $ "Weird use of state in " ++ show fname ++ ". In: " ++ show ins ++ " Out: " ++ show outs
  -- Join the create statements and the (optional) state_proc
  let statements = concat statementss ++ state_proc
  -- Create the architecture
  let arch = AST.ArchBody (mkVHDLBasicId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) statements
  let used_entities = concat used_entitiess
  return (arch, used_entities)
  where
    dobind :: (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The bind to process
              -> TranslatorSession ((Maybe CoreSyn.CoreBndr, Maybe CoreSyn.CoreBndr), ([AST.ConcSm], [CoreSyn.CoreBndr]))
              -- ^ ((Input state variable, output state variable), (statements, used entities))
    -- newtype unpacking is just a cast
    dobind (bndr, unpacked@(CoreSyn.Cast packed coercion)) 
      | hasStateType packed && not (hasStateType unpacked)
      = return ((Just bndr, Nothing), ([], []))
    -- With simplCore, newtype packing is just a cast
    dobind (bndr, packed@(CoreSyn.Cast unpacked@(CoreSyn.Var state) coercion)) 
      | hasStateType packed && not (hasStateType unpacked)
      = return ((Nothing, Just state), ([], []))
    -- Without simplCore, newtype packing uses a data constructor
    dobind (bndr, (CoreSyn.App (CoreSyn.App (CoreSyn.Var con) (CoreSyn.Type _)) (CoreSyn.Var state))) 
      | isStateCon con
      = return ((Nothing, Just state), ([], []))
    -- Anything else is handled by mkConcSm
    dobind bind = do
      sms <- mkConcSm bind
      return ((Nothing, Nothing), sms)

mkStateProcSm :: 
  (CoreSyn.CoreBndr, CoreSyn.CoreBndr) -- ^ The current and new state variables
  -> TranslatorSession [AST.ConcSm] -- ^ The resulting statements
mkStateProcSm (old, new) = do
  nonempty <- hasNonEmptyType old 
  if nonempty 
    then return [AST.CSPSm $ AST.ProcSm label [clockId,resetId] [statement]]
    else return []
  where
    label       = mkVHDLBasicId $ "state"
    rising_edge = AST.NSimple $ mkVHDLBasicId "rising_edge"
    wform       = AST.Wform [AST.WformElem (AST.PrimName $ varToVHDLName new) Nothing]
    clk_assign      = AST.SigAssign (varToVHDLName old) wform
    rising_edge_clk = AST.PrimFCall $ AST.FCall rising_edge [Nothing AST.:=>: (AST.ADName $ AST.NSimple clockId)]
    resetn_is_low  = (AST.PrimName $ AST.NSimple resetId) AST.:=: (AST.PrimLit "'0'")
    reset_statement = []
    clk_statement = [AST.ElseIf rising_edge_clk [clk_assign]]
    statement   = AST.IfSm resetn_is_low reset_statement clk_statement Nothing


-- | Transforms a core binding into a VHDL concurrent statement
mkConcSm ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The binding to process
  -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr]) 
  -- ^ The corresponding VHDL concurrent statements and entities
  --   instantiated.


-- Ignore Cast expressions, they should not longer have any meaning as long as
-- the type works out. Throw away state repacking
mkConcSm (bndr, to@(CoreSyn.Cast from ty))
  | hasStateType to && hasStateType from
  = return ([],[])
mkConcSm (bndr, CoreSyn.Cast expr ty) = mkConcSm (bndr, expr)

-- Simple a = b assignments are just like applications, but without arguments.
-- We can't just generate an unconditional assignment here, since b might be a
-- top level binding (e.g., a function with no arguments).
mkConcSm (bndr, CoreSyn.Var v) = do
  genApplication (Left bndr) v []

mkConcSm (bndr, app@(CoreSyn.App _ _))= do
  let (CoreSyn.Var f, args) = CoreSyn.collectArgs app
  let valargs = get_val_args (Var.varType f) args
  genApplication (Left bndr) f (map Left valargs)

-- A single alt case must be a selector. This means the scrutinee is a simple
-- variable, the alternative is a dataalt with a single non-wild binder that
-- is also returned.
mkConcSm (bndr, expr@(CoreSyn.Case (CoreSyn.Var scrut) b ty [alt])) 
                -- Don't generate VHDL for substate extraction
                | hasStateType bndr = return ([], [])
                | otherwise =
  case alt of
    (CoreSyn.DataAlt dc, bndrs, (CoreSyn.Var sel_bndr)) -> do
      bndrs' <- Monad.filterM hasNonEmptyType bndrs
      case List.elemIndex sel_bndr bndrs' of
        Just i -> do
          labels <- MonadState.lift tsType $ getFieldLabels (Id.idType scrut)
          let label = labels!!i
          let sel_name = mkSelectedName (varToVHDLName scrut) label
          let sel_expr = AST.PrimName sel_name
          return ([mkUncondAssign (Left bndr) sel_expr], [])
        Nothing -> error $ "\nVHDL.mkConcSM: Not in normal form: Not a selector case:\n" ++ (pprString expr)
      
    _ -> error $ "\nVHDL.mkConcSM: Not in normal form: Not a selector case:\n" ++ (pprString expr)

-- Multiple case alt are be conditional assignments and have only wild
-- binders in the alts and only variables in the case values and a variable
-- for a scrutinee. We check the constructor of the second alt, since the
-- first is the default case, if there is any.
mkConcSm (bndr, (CoreSyn.Case (CoreSyn.Var scrut) b ty [(_, _, CoreSyn.Var false), (con, _, CoreSyn.Var true)])) = do
  scrut' <- MonadState.lift tsType $ varToVHDLExpr scrut
  altcon <- MonadState.lift tsType $ altconToVHDLExpr con
  let cond_expr = scrut' AST.:=: altcon
  true_expr <- MonadState.lift tsType $ varToVHDLExpr true
  false_expr <- MonadState.lift tsType $ varToVHDLExpr false
  return ([mkCondAssign (Left bndr) cond_expr true_expr false_expr], [])

mkConcSm (_, (CoreSyn.Case (CoreSyn.Var _) _ _ alts)) = error "\nVHDL.mkConcSm: Not in normal form: Case statement with more than two alternatives"
mkConcSm (_, CoreSyn.Case _ _ _ _) = error "\nVHDL.mkConcSm: Not in normal form: Case statement has does not have a simple variable as scrutinee"
mkConcSm (bndr, expr) = error $ "\nVHDL.mkConcSM: Unsupported binding in let expression: " ++ pprString bndr ++ " = " ++ pprString expr

-----------------------------------------------------------------------------
-- Functions to generate VHDL for builtin functions
-----------------------------------------------------------------------------

-- | A function to wrap a builder-like function that expects its arguments to
-- be expressions.
genExprArgs wrap dst func args = do
  args' <- argsToVHDLExprs args
  wrap dst func args'

-- | Turn the all lefts into VHDL Expressions.
argsToVHDLExprs :: [Either CoreSyn.CoreExpr AST.Expr] -> TranslatorSession [AST.Expr]
argsToVHDLExprs = catMaybesM . (mapM argToVHDLExpr)

argToVHDLExpr :: Either CoreSyn.CoreExpr AST.Expr -> TranslatorSession (Maybe AST.Expr)
argToVHDLExpr (Left expr) = MonadState.lift tsType $ do
  let errmsg = "Generate.argToVHDLExpr: Using non-representable type? Should not happen!"
  ty_maybe <- vhdl_ty errmsg expr
  case ty_maybe of
    Just _ -> do
      vhdl_expr <- varToVHDLExpr $ exprToVar expr
      return $ Just vhdl_expr
    Nothing -> return $ Nothing

argToVHDLExpr (Right expr) = return $ Just expr

-- A function to wrap a builder-like function that generates no component
-- instantiations
genNoInsts ::
  (dst -> func -> args -> TranslatorSession [AST.ConcSm])
  -> (dst -> func -> args -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr]))
genNoInsts wrap dst func args = do
  concsms <- wrap dst func args
  return (concsms, [])

-- | A function to wrap a builder-like function that expects its arguments to
-- be variables.
genVarArgs ::
  (dst -> func -> [Var.Var] -> res)
  -> (dst -> func -> [Either CoreSyn.CoreExpr AST.Expr] -> res)
genVarArgs wrap dst func args = wrap dst func args'
  where
    args' = map exprToVar exprargs
    -- Check (rather crudely) that all arguments are CoreExprs
    (exprargs, []) = Either.partitionEithers args

-- | A function to wrap a builder-like function that expects its arguments to
-- be Literals
genLitArgs ::
  (dst -> func -> [Literal.Literal] -> TranslatorSession [AST.ConcSm])
  -> (dst -> func -> [Either CoreSyn.CoreExpr AST.Expr] -> TranslatorSession [AST.ConcSm])
genLitArgs wrap dst func args = do
  hscenv <- MonadState.lift tsType $ getA tsHscEnv
  let (exprargs, []) = Either.partitionEithers args
  -- FIXME: Check if we were passed an CoreSyn.App
  let litargs = concat (map (getLiterals hscenv) exprargs)
  let args' = map exprToLit litargs
  concsms <- wrap dst func args'
  return concsms    

-- | A function to wrap a builder-like function that produces an expression
-- and expects it to be assigned to the destination.
genExprRes ::
  ((Either CoreSyn.CoreBndr AST.VHDLName) -> func -> [arg] -> TranslatorSession AST.Expr)
  -> ((Either CoreSyn.CoreBndr AST.VHDLName) -> func -> [arg] -> TranslatorSession [AST.ConcSm])
genExprRes wrap dst func args = do
  expr <- wrap dst func args
  return $ [mkUncondAssign dst expr]

-- | Generate a binary operator application. The first argument should be a
-- constructor from the AST.Expr type, e.g. AST.And.
genOperator2 :: (AST.Expr -> AST.Expr -> AST.Expr) -> BuiltinBuilder 
genOperator2 op = genNoInsts $ genExprArgs $ genExprRes (genOperator2' op)
genOperator2' :: (AST.Expr -> AST.Expr -> AST.Expr) -> dst -> CoreSyn.CoreBndr -> [AST.Expr] -> TranslatorSession AST.Expr
genOperator2' op _ f [arg1, arg2] = return $ op arg1 arg2

-- | Generate a unary operator application
genOperator1 :: (AST.Expr -> AST.Expr) -> BuiltinBuilder 
genOperator1 op = genNoInsts $ genExprArgs $ genExprRes (genOperator1' op)
genOperator1' :: (AST.Expr -> AST.Expr) -> dst -> CoreSyn.CoreBndr -> [AST.Expr] -> TranslatorSession AST.Expr
genOperator1' op _ f [arg] = return $ op arg

-- | Generate a unary operator application
genNegation :: BuiltinBuilder 
genNegation = genNoInsts $ genVarArgs $ genExprRes genNegation'
genNegation' :: dst -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession AST.Expr
genNegation' _ f [arg] = do
  arg1 <- MonadState.lift tsType $ varToVHDLExpr arg
  let ty = Var.varType arg
  let (tycon, args) = Type.splitTyConApp ty
  let name = Name.getOccString (TyCon.tyConName tycon)
  case name of
    "SizedInt" -> return $ AST.Neg arg1
    otherwise -> error $ "\nGenerate.genNegation': Negation allowed for type: " ++ show name 

-- | Generate a function call from the destination binder, function name and a
-- list of expressions (its arguments)
genFCall :: Bool -> BuiltinBuilder 
genFCall switch = genNoInsts $ genExprArgs $ genExprRes (genFCall' switch)
genFCall' :: Bool -> Either CoreSyn.CoreBndr AST.VHDLName -> CoreSyn.CoreBndr -> [AST.Expr] -> TranslatorSession AST.Expr
genFCall' switch (Left res) f args = do
  let fname = varToString f
  let el_ty = if switch then (Var.varType res) else ((tfvec_elem . Var.varType) res)
  id <- MonadState.lift tsType $ vectorFunId el_ty fname
  return $ AST.PrimFCall $ AST.FCall (AST.NSimple id)  $
             map (\exp -> Nothing AST.:=>: AST.ADExpr exp) args
genFCall' _ (Right name) _ _ = error $ "\nGenerate.genFCall': Cannot generate builtin function call assigned to a VHDLName: " ++ show name

genFromSizedWord :: BuiltinBuilder
genFromSizedWord = genNoInsts $ genExprArgs genFromSizedWord'
genFromSizedWord' :: Either CoreSyn.CoreBndr AST.VHDLName -> CoreSyn.CoreBndr -> [AST.Expr] -> TranslatorSession [AST.ConcSm]
genFromSizedWord' (Left res) f args@[arg] = do
  return $ [mkUncondAssign (Left res) arg]
  -- let fname = varToString f
  -- return $ AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLBasicId toIntegerId))  $
  --            map (\exp -> Nothing AST.:=>: AST.ADExpr exp) args
genFromSizedWord' (Right name) _ _ = error $ "\nGenerate.genFromSizedWord': Cannot generate builtin function call assigned to a VHDLName: " ++ show name

genResize :: BuiltinBuilder
genResize = genNoInsts $ genExprArgs $ genExprRes genResize'
genResize' :: Either CoreSyn.CoreBndr AST.VHDLName -> CoreSyn.CoreBndr -> [AST.Expr] -> TranslatorSession AST.Expr
genResize' (Left res) f [arg] = do {
  ; let { ty = Var.varType res
        ; (tycon, args) = Type.splitTyConApp ty
        ; name = Name.getOccString (TyCon.tyConName tycon)
        } ;
  ; len <- case name of
      "SizedInt" -> MonadState.lift tsType $ tfp_to_int (sized_int_len_ty ty)
      "SizedWord" -> MonadState.lift tsType $ tfp_to_int (sized_word_len_ty ty)
  ; return $ AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLBasicId resizeId))
             [Nothing AST.:=>: AST.ADExpr arg, Nothing AST.:=>: AST.ADExpr( AST.PrimLit (show len))]
  }
genResize' (Right name) _ _ = error $ "\nGenerate.genFromSizedWord': Cannot generate builtin function call assigned to a VHDLName: " ++ show name

-- FIXME: I'm calling genLitArgs which is very specific function,
-- which needs to be fixed as well
genFromInteger :: BuiltinBuilder
genFromInteger = genNoInsts $ genLitArgs $ genExprRes genFromInteger'
genFromInteger' :: Either CoreSyn.CoreBndr AST.VHDLName -> CoreSyn.CoreBndr -> [Literal.Literal] -> TranslatorSession AST.Expr
genFromInteger' (Left res) f lits = do {
  ; let { ty = Var.varType res
        ; (tycon, args) = Type.splitTyConApp ty
        ; name = Name.getOccString (TyCon.tyConName tycon)
        } ;
  ; len <- case name of
    "SizedInt" -> MonadState.lift tsType $ tfp_to_int (sized_int_len_ty ty)
    "SizedWord" -> MonadState.lift tsType $ tfp_to_int (sized_word_len_ty ty)
    "RangedWord" -> do {
      ; bound <- MonadState.lift tsType $ tfp_to_int (ranged_word_bound_ty ty)
      ; return $ floor (logBase 2 (fromInteger (toInteger (bound)))) + 1
      }
  ; let fname = case name of "SizedInt" -> toSignedId ; "SizedWord" -> toUnsignedId ; "RangedWord" -> toUnsignedId
  ; return $ AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLBasicId fname))
            [Nothing AST.:=>: AST.ADExpr (AST.PrimLit (show (last lits))), Nothing AST.:=>: AST.ADExpr( AST.PrimLit (show len))]

  }

genFromInteger' (Right name) _ _ = error $ "\nGenerate.genFromInteger': Cannot generate builtin function call assigned to a VHDLName: " ++ show name

genSizedInt :: BuiltinBuilder
genSizedInt = genFromInteger

{-
-- | Generate a Builder for the builtin datacon TFVec
genTFVec :: BuiltinBuilder
genTFVec (Left res) f [Left (CoreSyn.Let (CoreSyn.Rec letBinders) letRes)] = do {
  -- Generate Assignments for all the binders
  ; letAssigns <- mapM genBinderAssign letBinders
  -- Generate assignments for the result (which might be another let binding)
  ; (resBinders,resAssignments) <- genResAssign letRes
  -- Get all the Assigned binders
  ; let assignedBinders = Maybe.catMaybes (map fst letAssigns)
  -- Make signal names for all the assigned binders
  ; sigs <- mapM (\x -> MonadState.lift tsType $ varToVHDLExpr x) (assignedBinders ++ resBinders)
  -- Assign all the signals to the resulting vector
  ; let { vecsigns = mkAggregateSignal sigs
        ; vecassign = mkUncondAssign (Left res) vecsigns
        } ;
  -- Generate all the signal declaration for the assigned binders
  ; sig_dec_maybes <- mapM mkSigDec (assignedBinders ++ resBinders)
  ; let { sig_decs = map (AST.BDISD) (Maybe.catMaybes $ sig_dec_maybes)
  -- Setup the VHDL Block
        ; block_label = mkVHDLExtId ("TFVec_" ++ show (varToString res))
        ; block = AST.BlockSm block_label [] (AST.PMapAspect []) sig_decs ((concat (map snd letAssigns)) ++ resAssignments ++ [vecassign])
        } ;
  -- Return the block statement coressponding to the TFVec literal
  ; return $ [AST.CSBSm block]
  }
  where
    genBinderAssign :: (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -> TranslatorSession (Maybe CoreSyn.CoreBndr, [AST.ConcSm])
    -- For now we only translate applications
    genBinderAssign (bndr, app@(CoreSyn.App _ _)) = do
      let (CoreSyn.Var f, args) = CoreSyn.collectArgs app
      let valargs = get_val_args (Var.varType f) args
      apps <- genApplication (Left bndr) f (map Left valargs)
      return (Just bndr, apps)
    genBinderAssign _ = return (Nothing,[])
    genResAssign :: CoreSyn.CoreExpr -> TranslatorSession ([CoreSyn.CoreBndr], [AST.ConcSm])
    genResAssign app@(CoreSyn.App _ letexpr) = do
      case letexpr of
        (CoreSyn.Let (CoreSyn.Rec letbndrs) letres) -> do
          letapps <- mapM genBinderAssign letbndrs
          let bndrs = Maybe.catMaybes (map fst letapps)
          let app = (map snd letapps)
          (vars, apps) <- genResAssign letres
          return ((bndrs ++ vars),((concat app) ++ apps))
        otherwise -> return ([],[])
    genResAssign _ = return ([],[])

genTFVec (Left res) f [Left app@(CoreSyn.App _ _)] = do {
  ; let { elems = reduceCoreListToHsList app
  -- Make signal names for all the binders
        ; binders = map (\expr -> case expr of 
                          (CoreSyn.Var b) -> b
                          otherwise -> error $ "\nGenerate.genTFVec: Cannot generate TFVec: " 
                            ++ show res ++ ", with elems:\n" ++ show elems ++ "\n" ++ pprString elems) elems
        } ;
  ; sigs <- mapM (\x -> MonadState.lift tsType $ varToVHDLExpr x) binders
  -- Assign all the signals to the resulting vector
  ; let { vecsigns = mkAggregateSignal sigs
        ; vecassign = mkUncondAssign (Left res) vecsigns
  -- Setup the VHDL Block
        ; block_label = mkVHDLExtId ("TFVec_" ++ show (varToString res))
        ; block = AST.BlockSm block_label [] (AST.PMapAspect []) [] [vecassign]
        } ;
  -- Return the block statement coressponding to the TFVec literal
  ; return $ [AST.CSBSm block]
  }
  
genTFVec (Left name) _ [Left xs] = error $ "\nGenerate.genTFVec: Cannot generate TFVec: " ++ show name ++ ", with elems:\n" ++ show xs ++ "\n" ++ pprString xs

genTFVec (Right name) _ _ = error $ "\nGenerate.genTFVec: Cannot generate TFVec assigned to VHDLName: " ++ show name
-}
-- | Generate a generate statement for the builtin function "map"
genMap :: BuiltinBuilder
genMap (Left res) f [Left mapped_f, Left (CoreSyn.Var arg)] = do {
  -- mapped_f must be a CoreExpr (since we can't represent functions as VHDL
  -- expressions). arg must be a CoreExpr (and should be a CoreSyn.Var), since
  -- we must index it (which we couldn't if it was a VHDL Expr, since only
  -- VHDLNames can be indexed).
  -- Setup the generate scheme
  ; len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) res
          -- TODO: Use something better than varToString
  ; let { label       = mkVHDLExtId ("mapVector" ++ (varToString res))
        ; n_id        = mkVHDLBasicId "n"
        ; n_expr      = idToVHDLExpr n_id
        ; range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
        ; genScheme   = AST.ForGn n_id range
          -- Create the content of the generate statement: Applying the mapped_f to
          -- each of the elements in arg, storing to each element in res
        ; resname     = mkIndexedName (varToVHDLName res) n_expr
        ; argexpr     = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName arg) n_expr
        ; (CoreSyn.Var real_f, already_mapped_args) = CoreSyn.collectArgs mapped_f
        ; valargs = get_val_args (Var.varType real_f) already_mapped_args
        } ;
  ; (app_concsms, used) <- genApplication (Right resname) real_f (map Left valargs ++ [Right argexpr])
    -- Return the generate statement
  ; return ([AST.CSGSm $ AST.GenerateSm label genScheme [] app_concsms], used)
  }

genMap' (Right name) _ _ = error $ "\nGenerate.genMap': Cannot generate map function call assigned to a VHDLName: " ++ show name
    
genZipWith :: BuiltinBuilder
genZipWith = genVarArgs genZipWith'
genZipWith' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr])
genZipWith' (Left res) f args@[zipped_f, arg1, arg2] = do {
  -- Setup the generate scheme
  ; len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) res
          -- TODO: Use something better than varToString
  ; let { label       = mkVHDLExtId ("zipWithVector" ++ (varToString res))
        ; n_id        = mkVHDLBasicId "n"
        ; n_expr      = idToVHDLExpr n_id
        ; range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
        ; genScheme   = AST.ForGn n_id range
          -- Create the content of the generate statement: Applying the zipped_f to
          -- each of the elements in arg1 and arg2, storing to each element in res
        ; resname     = mkIndexedName (varToVHDLName res) n_expr
        ; argexpr1    = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName arg1) n_expr
        ; argexpr2    = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName arg2) n_expr
        } ;
  ; (app_concsms, used) <- genApplication (Right resname) zipped_f [Right argexpr1, Right argexpr2]
    -- Return the generate functions
  ; return ([AST.CSGSm $ AST.GenerateSm label genScheme [] app_concsms], used)
  }

genFoldl :: BuiltinBuilder
genFoldl = genFold True

genFoldr :: BuiltinBuilder
genFoldr = genFold False

genFold :: Bool -> BuiltinBuilder
genFold left = genVarArgs (genFold' left)

genFold' :: Bool -> (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr])
genFold' left res f args@[folded_f , start ,vec]= do
  len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty (Var.varType vec))
  genFold'' len left res f args

genFold'' :: Int -> Bool -> (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr])
-- Special case for an empty input vector, just assign start to res
genFold'' len left (Left res) _ [_, start, vec] | len == 0 = do
  arg <- MonadState.lift tsType $ varToVHDLExpr start
  return ([mkUncondAssign (Left res) arg], [])
    
genFold'' len left (Left res) f [folded_f, start, vec] = do
  -- The vector length
  --len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) vec
  -- An expression for len-1
  let len_min_expr = (AST.PrimLit $ show (len-1))
  -- evec is (TFVec n), so it still needs an element type
  let (nvec, _) = Type.splitAppTy (Var.varType vec)
  -- Put the type of the start value in nvec, this will be the type of our
  -- temporary vector
  let tmp_ty = Type.mkAppTy nvec (Var.varType start)
  let error_msg = "\nGenerate.genFold': Can not construct temp vector for element type: " ++ pprString tmp_ty 
  -- TODO: Handle Nothing
  Just tmp_vhdl_ty <- MonadState.lift tsType $ vhdl_ty error_msg tmp_ty
  -- Setup the generate scheme
  let gen_label = mkVHDLExtId ("foldlVector" ++ (varToString vec))
  let block_label = mkVHDLExtId ("foldlVector" ++ (varToString res))
  let gen_range = if left then AST.ToRange (AST.PrimLit "0") len_min_expr
                  else AST.DownRange len_min_expr (AST.PrimLit "0")
  let gen_scheme   = AST.ForGn n_id gen_range
  -- Make the intermediate vector
  let  tmp_dec     = AST.BDISD $ AST.SigDec tmp_id tmp_vhdl_ty Nothing
  -- Create the generate statement
  cells' <- sequence [genFirstCell, genOtherCell]
  let (cells, useds) = unzip cells'
  let gen_sm = AST.GenerateSm gen_label gen_scheme [] (map AST.CSGSm cells)
  -- Assign tmp[len-1] or tmp[0] to res
  let out_assign = mkUncondAssign (Left res) $ vhdlNameToVHDLExpr (if left then
                    (mkIndexedName tmp_name (AST.PrimLit $ show (len-1))) else
                    (mkIndexedName tmp_name (AST.PrimLit "0")))      
  let block = AST.BlockSm block_label [] (AST.PMapAspect []) [tmp_dec] [AST.CSGSm gen_sm, out_assign]
  return ([AST.CSBSm block], concat useds)
  where
    -- An id for the counter
    n_id = mkVHDLBasicId "n"
    n_cur = idToVHDLExpr n_id
    -- An expression for previous n
    n_prev = if left then (n_cur AST.:-: (AST.PrimLit "1"))
                     else (n_cur AST.:+: (AST.PrimLit "1"))
    -- An id for the tmp result vector
    tmp_id = mkVHDLBasicId "tmp"
    tmp_name = AST.NSimple tmp_id
    -- Generate parts of the fold
    genFirstCell, genOtherCell :: TranslatorSession (AST.GenerateSm, [CoreSyn.CoreBndr])
    genFirstCell = do
      len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) vec
      let cond_label = mkVHDLExtId "firstcell"
      -- if n == 0 or n == len-1
      let cond_scheme = AST.IfGn $ n_cur AST.:=: (if left then (AST.PrimLit "0")
                                                  else (AST.PrimLit $ show (len-1)))
      -- Output to tmp[current n]
      let resname = mkIndexedName tmp_name n_cur
      -- Input from start
      argexpr1 <- MonadState.lift tsType $ varToVHDLExpr start
      -- Input from vec[current n]
      let argexpr2 = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName vec) n_cur
      (app_concsms, used) <- genApplication (Right resname) folded_f  ( if left then
                                                                  [Right argexpr1, Right argexpr2]
                                                                else
                                                                  [Right argexpr2, Right argexpr1]
                                                              )
      -- Return the conditional generate part
      return $ (AST.GenerateSm cond_label cond_scheme [] app_concsms, used)

    genOtherCell = do
      len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) vec
      let cond_label = mkVHDLExtId "othercell"
      -- if n > 0 or n < len-1
      let cond_scheme = AST.IfGn $ n_cur AST.:/=: (if left then (AST.PrimLit "0")
                                                   else (AST.PrimLit $ show (len-1)))
      -- Output to tmp[current n]
      let resname = mkIndexedName tmp_name n_cur
      -- Input from tmp[previous n]
      let argexpr1 = vhdlNameToVHDLExpr $ mkIndexedName tmp_name n_prev
      -- Input from vec[current n]
      let argexpr2 = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName vec) n_cur
      (app_concsms, used) <- genApplication (Right resname) folded_f  ( if left then
                                                                  [Right argexpr1, Right argexpr2]
                                                                else
                                                                  [Right argexpr2, Right argexpr1]
                                                              )
      -- Return the conditional generate part
      return $ (AST.GenerateSm cond_label cond_scheme [] app_concsms, used)

-- | Generate a generate statement for the builtin function "zip"
genZip :: BuiltinBuilder
genZip = genNoInsts $ genVarArgs genZip'
genZip' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession [AST.ConcSm]
genZip' (Left res) f args@[arg1, arg2] = do {
    -- Setup the generate scheme
  ; len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) res
          -- TODO: Use something better than varToString
  ; let { label           = mkVHDLExtId ("zipVector" ++ (varToString res))
        ; n_id            = mkVHDLBasicId "n"
        ; n_expr          = idToVHDLExpr n_id
        ; range           = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
        ; genScheme       = AST.ForGn n_id range
        ; resname'        = mkIndexedName (varToVHDLName res) n_expr
        ; argexpr1        = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName arg1) n_expr
        ; argexpr2        = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName arg2) n_expr
        } ; 
  ; labels <- MonadState.lift tsType $ getFieldLabels (tfvec_elem (Var.varType res))
  ; let { resnameA    = mkSelectedName resname' (labels!!0)
        ; resnameB    = mkSelectedName resname' (labels!!1)
        ; resA_assign = mkUncondAssign (Right resnameA) argexpr1
        ; resB_assign = mkUncondAssign (Right resnameB) argexpr2
        } ;
    -- Return the generate functions
  ; return [AST.CSGSm $ AST.GenerateSm label genScheme [] [resA_assign,resB_assign]]
  }
  
-- | Generate a generate statement for the builtin function "fst"
genFst :: BuiltinBuilder
genFst = genNoInsts $ genVarArgs genFst'
genFst' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession [AST.ConcSm]
genFst' (Left res) f args@[arg] = do {
  ; labels <- MonadState.lift tsType $ getFieldLabels (Var.varType arg)
  ; let { argexpr'    = varToVHDLName arg
        ; argexprA    = vhdlNameToVHDLExpr $ mkSelectedName argexpr' (labels!!0)
        ; assign      = mkUncondAssign (Left res) argexprA
        } ;
    -- Return the generate functions
  ; return [assign]
  }
  
-- | Generate a generate statement for the builtin function "snd"
genSnd :: BuiltinBuilder
genSnd = genNoInsts $ genVarArgs genSnd'
genSnd' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession [AST.ConcSm]
genSnd' (Left res) f args@[arg] = do {
  ; labels <- MonadState.lift tsType $ getFieldLabels (Var.varType arg)
  ; let { argexpr'    = varToVHDLName arg
        ; argexprB    = vhdlNameToVHDLExpr $ mkSelectedName argexpr' (labels!!1)
        ; assign      = mkUncondAssign (Left res) argexprB
        } ;
    -- Return the generate functions
  ; return [assign]
  }
    
-- | Generate a generate statement for the builtin function "unzip"
genUnzip :: BuiltinBuilder
genUnzip = genNoInsts $ genVarArgs genUnzip'
genUnzip' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession [AST.ConcSm]
genUnzip' (Left res) f args@[arg] = do {
    -- Setup the generate scheme
  ; len <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) arg
    -- TODO: Use something better than varToString
  ; let { label           = mkVHDLExtId ("unzipVector" ++ (varToString res))
        ; n_id            = mkVHDLBasicId "n"
        ; n_expr          = idToVHDLExpr n_id
        ; range           = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
        ; genScheme       = AST.ForGn n_id range
        ; resname'        = varToVHDLName res
        ; argexpr'        = mkIndexedName (varToVHDLName arg) n_expr
        } ;
  ; reslabels <- MonadState.lift tsType $ getFieldLabels (Var.varType res)
  ; arglabels <- MonadState.lift tsType $ getFieldLabels (tfvec_elem (Var.varType arg))
  ; let { resnameA    = mkIndexedName (mkSelectedName resname' (reslabels!!0)) n_expr
        ; resnameB    = mkIndexedName (mkSelectedName resname' (reslabels!!1)) n_expr
        ; argexprA    = vhdlNameToVHDLExpr $ mkSelectedName argexpr' (arglabels!!0)
        ; argexprB    = vhdlNameToVHDLExpr $ mkSelectedName argexpr' (arglabels!!1)
        ; resA_assign = mkUncondAssign (Right resnameA) argexprA
        ; resB_assign = mkUncondAssign (Right resnameB) argexprB
        } ;
    -- Return the generate functions
  ; return [AST.CSGSm $ AST.GenerateSm label genScheme [] [resA_assign,resB_assign]]
  }

genCopy :: BuiltinBuilder 
genCopy = genNoInsts $ genVarArgs genCopy'
genCopy' :: (Either CoreSyn.CoreBndr AST.VHDLName ) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession [AST.ConcSm]
genCopy' (Left res) f args@[arg] =
  let
    resExpr = AST.Aggregate [AST.ElemAssoc (Just AST.Others) 
                (AST.PrimName $ (varToVHDLName arg))]
    out_assign = mkUncondAssign (Left res) resExpr
  in 
    return [out_assign]
    
genConcat :: BuiltinBuilder
genConcat = genNoInsts $ genVarArgs genConcat'
genConcat' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession [AST.ConcSm]
genConcat' (Left res) f args@[arg] = do {
    -- Setup the generate scheme
  ; len1 <- MonadState.lift tsType $ tfp_to_int $ (tfvec_len_ty . Var.varType) arg
  ; let (_, nvec) = Type.splitAppTy (Var.varType arg)
  ; len2 <- MonadState.lift tsType $ tfp_to_int $ tfvec_len_ty nvec
          -- TODO: Use something better than varToString
  ; let { label       = mkVHDLExtId ("concatVector" ++ (varToString res))
        ; n_id        = mkVHDLBasicId "n"
        ; n_expr      = idToVHDLExpr n_id
        ; fromRange   = n_expr AST.:*: (AST.PrimLit $ show len2)
        ; genScheme   = AST.ForGn n_id range
          -- Create the content of the generate statement: Applying the mapped_f to
          -- each of the elements in arg, storing to each element in res
        ; toRange     = (n_expr AST.:*: (AST.PrimLit $ show len2)) AST.:+: (AST.PrimLit $ show (len2-1))
        ; range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len1-1))
        ; resname     = vecSlice fromRange toRange
        ; argexpr     = vhdlNameToVHDLExpr $ mkIndexedName (varToVHDLName arg) n_expr
        ; out_assign  = mkUncondAssign (Right resname) argexpr
        } ;
    -- Return the generate statement
  ; return [AST.CSGSm $ AST.GenerateSm label genScheme [] [out_assign]]
  }
  where
    vecSlice init last =  AST.NSlice (AST.SliceName (varToVHDLName res) 
                            (AST.ToRange init last))

genIteraten :: BuiltinBuilder
genIteraten dst f args = genIterate dst f (tail args)

genIterate :: BuiltinBuilder
genIterate = genIterateOrGenerate True

genGeneraten :: BuiltinBuilder
genGeneraten dst f args = genGenerate dst f (tail args)

genGenerate :: BuiltinBuilder
genGenerate = genIterateOrGenerate False

genIterateOrGenerate :: Bool -> BuiltinBuilder
genIterateOrGenerate iter = genVarArgs (genIterateOrGenerate' iter)

genIterateOrGenerate' :: Bool -> (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr])
genIterateOrGenerate' iter (Left res) f args = do
  len <- MonadState.lift tsType $ tfp_to_int ((tfvec_len_ty . Var.varType) res)
  genIterateOrGenerate'' len iter (Left res) f args

genIterateOrGenerate'' :: Int -> Bool -> (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr])
-- Special case for an empty input vector, just assign start to res
genIterateOrGenerate'' len iter (Left res) _ [app_f, start] | len == 0 = return ([mkUncondAssign (Left res) (AST.PrimLit "\"\"")], [])

genIterateOrGenerate'' len iter (Left res) f [app_f, start] = do
  -- The vector length
  -- len <- MonadState.lift tsType $ tfp_to_int ((tfvec_len_ty . Var.varType) res)
  -- An expression for len-1
  let len_min_expr = (AST.PrimLit $ show (len-1))
  -- -- evec is (TFVec n), so it still needs an element type
  -- let (nvec, _) = splitAppTy (Var.varType vec)
  -- -- Put the type of the start value in nvec, this will be the type of our
  -- -- temporary vector
  let tmp_ty = Var.varType res
  let error_msg = "\nGenerate.genFold': Can not construct temp vector for element type: " ++ pprString tmp_ty 
  -- TODO: Handle Nothing
  Just tmp_vhdl_ty <- MonadState.lift tsType $ vhdl_ty error_msg tmp_ty
  -- Setup the generate scheme
  let gen_label = mkVHDLExtId ("iterateVector" ++ (varToString start))
  let block_label = mkVHDLExtId ("iterateVector" ++ (varToString res))
  let gen_range = AST.ToRange (AST.PrimLit "0") len_min_expr
  let gen_scheme   = AST.ForGn n_id gen_range
  -- Make the intermediate vector
  let  tmp_dec     = AST.BDISD $ AST.SigDec tmp_id tmp_vhdl_ty Nothing
  -- Create the generate statement
  cells' <- sequence [genFirstCell, genOtherCell]
  let (cells, useds) = unzip cells'
  let gen_sm = AST.GenerateSm gen_label gen_scheme [] (map AST.CSGSm cells)
  -- Assign tmp[len-1] or tmp[0] to res
  let out_assign = mkUncondAssign (Left res) $ vhdlNameToVHDLExpr tmp_name    
  let block = AST.BlockSm block_label [] (AST.PMapAspect []) [tmp_dec] [AST.CSGSm gen_sm, out_assign]
  return ([AST.CSBSm block], concat useds)
  where
    -- An id for the counter
    n_id = mkVHDLBasicId "n"
    n_cur = idToVHDLExpr n_id
    -- An expression for previous n
    n_prev = n_cur AST.:-: (AST.PrimLit "1")
    -- An id for the tmp result vector
    tmp_id = mkVHDLBasicId "tmp"
    tmp_name = AST.NSimple tmp_id
    -- Generate parts of the fold
    genFirstCell, genOtherCell :: TranslatorSession (AST.GenerateSm, [CoreSyn.CoreBndr])
    genFirstCell = do
      let cond_label = mkVHDLExtId "firstcell"
      -- if n == 0 or n == len-1
      let cond_scheme = AST.IfGn $ n_cur AST.:=: (AST.PrimLit "0")
      -- Output to tmp[current n]
      let resname = mkIndexedName tmp_name n_cur
      -- Input from start
      argexpr <- MonadState.lift tsType $ varToVHDLExpr start
      let startassign = mkUncondAssign (Right resname) argexpr
      (app_concsms, used) <- genApplication (Right resname) app_f  [Right argexpr]
      -- Return the conditional generate part
      let gensm = AST.GenerateSm cond_label cond_scheme [] (if iter then 
                                                          [startassign]
                                                         else 
                                                          app_concsms
                                                        )
      return (gensm, used)

    genOtherCell = do
      let cond_label = mkVHDLExtId "othercell"
      -- if n > 0 or n < len-1
      let cond_scheme = AST.IfGn $ n_cur AST.:/=: (AST.PrimLit "0")
      -- Output to tmp[current n]
      let resname = mkIndexedName tmp_name n_cur
      -- Input from tmp[previous n]
      let argexpr = vhdlNameToVHDLExpr $ mkIndexedName tmp_name n_prev
      (app_concsms, used) <- genApplication (Right resname) app_f [Right argexpr]
      -- Return the conditional generate part
      return $ (AST.GenerateSm cond_label cond_scheme [] app_concsms, used)

genBlockRAM :: BuiltinBuilder
genBlockRAM = genNoInsts $ genExprArgs genBlockRAM'

genBlockRAM' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [AST.Expr] -> TranslatorSession [AST.ConcSm]
genBlockRAM' (Left res) f args@[data_in,rdaddr,wraddr,wrenable] = do
  -- Get the ram type
  let (tup,data_out) = Type.splitAppTy (Var.varType res)
  let (tup',ramvec) = Type.splitAppTy tup
  let Just realram = Type.coreView ramvec
  let Just (tycon, types) = Type.splitTyConApp_maybe realram
  Just ram_vhdl_ty <- MonadState.lift tsType $ vhdl_ty "wtf" (head types)
  -- Make the intermediate vector
  let ram_dec = AST.BDISD $ AST.SigDec ram_id ram_vhdl_ty Nothing
  -- Get the data_out name
  reslabels <- MonadState.lift tsType $ getFieldLabels (Var.varType res)
  let resname' = varToVHDLName res
  let resname = mkSelectedName resname' (reslabels!!0)
  let rdaddr_int = genExprFCall (mkVHDLBasicId toIntegerId) rdaddr
  let argexpr = vhdlNameToVHDLExpr $ mkIndexedName (AST.NSimple ram_id) rdaddr_int
  let assign = mkUncondAssign (Right resname) argexpr
  let block_label = mkVHDLExtId ("blockRAM" ++ (varToString res))
  let block = AST.BlockSm block_label [] (AST.PMapAspect []) [ram_dec] [assign, mkUpdateProcSm]
  return [AST.CSBSm block]
  where
    ram_id = mkVHDLBasicId "ram"
    mkUpdateProcSm :: AST.ConcSm
    mkUpdateProcSm = AST.CSPSm $ AST.ProcSm proclabel [clockId] [statement]
      where
        proclabel   = mkVHDLBasicId "updateRAM"
        rising_edge = mkVHDLBasicId "rising_edge"
        wraddr_int  = genExprFCall (mkVHDLBasicId toIntegerId) wraddr
        ramloc      = mkIndexedName (AST.NSimple ram_id) wraddr_int
        wform       = AST.Wform [AST.WformElem data_in Nothing]
        ramassign      = AST.SigAssign ramloc wform
        rising_edge_clk = genExprFCall rising_edge (AST.PrimName $ AST.NSimple clockId)
        statement   = AST.IfSm (AST.And rising_edge_clk wrenable) [ramassign] [] Nothing

-----------------------------------------------------------------------------
-- Function to generate VHDL for applications
-----------------------------------------------------------------------------
genApplication ::
  (Either CoreSyn.CoreBndr AST.VHDLName) -- ^ Where to store the result?
  -> CoreSyn.CoreBndr -- ^ The function to apply
  -> [Either CoreSyn.CoreExpr AST.Expr] -- ^ The arguments to apply
  -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr]) 
  -- ^ The corresponding VHDL concurrent statements and entities
  --   instantiated.
genApplication dst f args = do
  case Var.isGlobalId f of
    False -> do 
      top <- isTopLevelBinder f
      case top of
        True -> do
          -- Local binder that references a top level binding.  Generate a
          -- component instantiation.
          signature <- getEntity f
          args' <- argsToVHDLExprs args
          let entity_id = ent_id signature
          -- TODO: Using show here isn't really pretty, but we'll need some
          -- unique-ish value...
          let label = "comp_ins_" ++ (either (prettyShow . varToVHDLName) prettyShow) dst
          let portmaps = mkAssocElems args' ((either varToVHDLName id) dst) signature
          return ([mkComponentInst label entity_id portmaps], [f])
        False -> do
          -- Not a top level binder, so this must be a local variable reference.
          -- It should have a representable type (and thus, no arguments) and a
          -- signal should be generated for it. Just generate an unconditional
          -- assignment here.
          f' <- MonadState.lift tsType $ varToVHDLExpr f
          return $ ([mkUncondAssign dst f'], [])
    True ->
      case Var.idDetails f of
        IdInfo.DataConWorkId dc -> case dst of
          -- It's a datacon. Create a record from its arguments.
          Left bndr -> do
            -- We have the bndr, so we can get at the type
            labels <- MonadState.lift tsType $ getFieldLabels (Var.varType bndr)
            args' <- argsToVHDLExprs args
            return $ (zipWith mkassign labels $ args', [])
            where
              mkassign :: AST.VHDLId -> AST.Expr -> AST.ConcSm
              mkassign label arg =
                let sel_name = mkSelectedName ((either varToVHDLName id) dst) label in
                mkUncondAssign (Right sel_name) arg
          Right _ -> error $ "\nGenerate.genApplication: Can't generate dataconstructor application without an original binder"
        IdInfo.DataConWrapId dc -> case dst of
          -- It's a datacon. Create a record from its arguments.
          Left bndr -> do 
            case (Map.lookup (varToString f) globalNameTable) of
             Just (arg_count, builder) ->
              if length args == arg_count then
                builder dst f args
              else
                error $ "\nGenerate.genApplication(DataConWrapId): Incorrect number of arguments to builtin function: " ++ pprString f ++ " Args: " ++ show args
             Nothing -> error $ "\nGenerate.genApplication: Can't generate dataconwrapper: " ++ (show dc)
          Right _ -> error $ "\nGenerate.genApplication: Can't generate dataconwrapper application without an original binder"
        IdInfo.VanillaId -> do
          -- It's a global value imported from elsewhere. These can be builtin
          -- functions. Look up the function name in the name table and execute
          -- the associated builder if there is any and the argument count matches
          -- (this should always be the case if it typechecks, but just to be
          -- sure...).
          case (Map.lookup (varToString f) globalNameTable) of
            Just (arg_count, builder) ->
              if length args == arg_count then
                builder dst f args
              else
                error $ "\nGenerate.genApplication(VanillaId): Incorrect number of arguments to builtin function: " ++ pprString f ++ " Args: " ++ show args
            Nothing -> do
              top <- isTopLevelBinder f
              case top of
                True -> do
                  -- Local binder that references a top level binding.  Generate a
                  -- component instantiation.
                  signature <- getEntity f
                  args' <- argsToVHDLExprs args
                  let entity_id = ent_id signature
                  -- TODO: Using show here isn't really pretty, but we'll need some
                  -- unique-ish value...
                  let label = "comp_ins_" ++ (either show prettyShow) dst
                  let portmaps = mkAssocElems args' ((either varToVHDLName id) dst) signature
                  return ([mkComponentInst label entity_id portmaps], [f])
                False -> do
                  -- Not a top level binder, so this must be a local variable reference.
                  -- It should have a representable type (and thus, no arguments) and a
                  -- signal should be generated for it. Just generate an unconditional
                  -- assignment here.
                  -- FIXME : I DONT KNOW IF THE ABOVE COMMENT HOLDS HERE, SO FOR NOW JUST ERROR!
                  -- f' <- MonadState.lift tsType $ varToVHDLExpr f
                  --                   return $ ([mkUncondAssign dst f'], [])
                  error $ ("\nGenerate.genApplication(VanillaId): Using function from another module that is not a known builtin: " ++ (pprString f))
        IdInfo.ClassOpId cls -> do
          -- FIXME: Not looking for what instance this class op is called for
          -- Is quite stupid of course.
          case (Map.lookup (varToString f) globalNameTable) of
            Just (arg_count, builder) ->
              if length args == arg_count then
                builder dst f args
              else
                error $ "\nGenerate.genApplication(ClassOpId): Incorrect number of arguments to builtin function: " ++ pprString f ++ " Args: " ++ show args
            Nothing -> error $ "\nGenerate.genApplication(ClassOpId): Using function from another module that is not a known builtin: " ++ pprString f
        details -> error $ "\nGenerate.genApplication: Calling unsupported function " ++ pprString f ++ " with GlobalIdDetails " ++ pprString details

-----------------------------------------------------------------------------
-- Functions to generate functions dealing with vectors.
-----------------------------------------------------------------------------

-- Returns the VHDLId of the vector function with the given name for the given
-- element type. Generates -- this function if needed.
vectorFunId :: Type.Type -> String -> TypeSession AST.VHDLId
vectorFunId el_ty fname = do
  let error_msg = "\nGenerate.vectorFunId: Can not construct vector function for element: " ++ pprString el_ty
  -- TODO: Handle the Nothing case?
  Just elemTM <- vhdl_ty error_msg el_ty
  -- TODO: This should not be duplicated from mk_vector_ty. Probably but it in
  -- the VHDLState or something.
  let vectorTM = mkVHDLExtId $ "vector_" ++ (AST.fromVHDLId elemTM)
  typefuns <- getA tsTypeFuns
  case Map.lookup (OrdType el_ty, fname) typefuns of
    -- Function already generated, just return it
    Just (id, _) -> return id
    -- Function not generated yet, generate it
    Nothing -> do
      let functions = genUnconsVectorFuns elemTM vectorTM
      case lookup fname functions of
        Just body -> do
          modA tsTypeFuns $ Map.insert (OrdType el_ty, fname) (function_id, (fst body))
          mapM_ (vectorFunId el_ty) (snd body)
          return function_id
        Nothing -> error $ "\nGenerate.vectorFunId: I don't know how to generate vector function " ++ fname
  where
    function_id = mkVHDLExtId fname

genUnconsVectorFuns :: AST.TypeMark -- ^ type of the vector elements
                    -> AST.TypeMark -- ^ type of the vector
                    -> [(String, (AST.SubProgBody, [String]))]
genUnconsVectorFuns elemTM vectorTM  = 
  [ (exId, (AST.SubProgBody exSpec      []                  [exExpr],[]))
  , (replaceId, (AST.SubProgBody replaceSpec [AST.SPVD replaceVar] [replaceExpr1,replaceExpr2,replaceRet],[]))
  , (lastId, (AST.SubProgBody lastSpec    []                  [lastExpr],[]))
  , (initId, (AST.SubProgBody initSpec    [AST.SPVD initVar]  [initExpr, initRet],[]))
  , (minimumId, (AST.SubProgBody minimumSpec [] [minimumExpr],[]))
  , (takeId, (AST.SubProgBody takeSpec    [AST.SPVD takeVar]  [takeExpr, takeRet],[minimumId]))
  , (dropId, (AST.SubProgBody dropSpec    [AST.SPVD dropVar]  [dropExpr, dropRet],[]))
  , (plusgtId, (AST.SubProgBody plusgtSpec  [AST.SPVD plusgtVar] [plusgtExpr, plusgtRet],[]))
  , (emptyId, (AST.SubProgBody emptySpec   [AST.SPVD emptyVar] [emptyExpr],[]))
  , (singletonId, (AST.SubProgBody singletonSpec [AST.SPVD singletonVar] [singletonRet],[]))
  , (copynId, (AST.SubProgBody copynSpec    [AST.SPVD copynVar]      [copynExpr],[]))
  , (selId, (AST.SubProgBody selSpec  [AST.SPVD selVar] [selFor, selRet],[]))
  , (ltplusId, (AST.SubProgBody ltplusSpec [AST.SPVD ltplusVar] [ltplusExpr, ltplusRet],[]))  
  , (plusplusId, (AST.SubProgBody plusplusSpec [AST.SPVD plusplusVar] [plusplusExpr, plusplusRet],[]))
  , (lengthTId, (AST.SubProgBody lengthTSpec [] [lengthTExpr],[]))
  , (shiftlId, (AST.SubProgBody shiftlSpec [AST.SPVD shiftlVar] [shiftlExpr, shiftlRet], [initId]))
  , (shiftrId, (AST.SubProgBody shiftrSpec [AST.SPVD shiftrVar] [shiftrExpr, shiftrRet], [tailId]))
  , (nullId, (AST.SubProgBody nullSpec [] [nullExpr], []))
  , (rotlId, (AST.SubProgBody rotlSpec [AST.SPVD rotlVar] [rotlExpr, rotlRet], [nullId, lastId, initId]))
  , (rotrId, (AST.SubProgBody rotrSpec [AST.SPVD rotrVar] [rotrExpr, rotrRet], [nullId, tailId, headId]))
  , (reverseId, (AST.SubProgBody reverseSpec [AST.SPVD reverseVar] [reverseFor, reverseRet], []))
  ]
  where 
    ixPar   = AST.unsafeVHDLBasicId "ix"
    vecPar  = AST.unsafeVHDLBasicId "vec"
    vec1Par = AST.unsafeVHDLBasicId "vec1"
    vec2Par = AST.unsafeVHDLBasicId "vec2"
    nPar    = AST.unsafeVHDLBasicId "n"
    leftPar = AST.unsafeVHDLBasicId "nLeft"
    rightPar = AST.unsafeVHDLBasicId "nRight"
    iId     = AST.unsafeVHDLBasicId "i"
    iPar    = iId
    aPar    = AST.unsafeVHDLBasicId "a"
    fPar = AST.unsafeVHDLBasicId "f"
    sPar = AST.unsafeVHDLBasicId "s"
    resId   = AST.unsafeVHDLBasicId "res"    
    exSpec = AST.Function (mkVHDLExtId exId) [AST.IfaceVarDec vecPar vectorTM,
                               AST.IfaceVarDec ixPar  unsignedTM] elemTM
    exExpr = AST.ReturnSm (Just $ AST.PrimName $ AST.NIndexed 
              (AST.IndexedName (AST.NSimple vecPar) [genExprFCall (mkVHDLBasicId toIntegerId) (AST.PrimName $ AST.NSimple $ ixPar)]))
    replaceSpec = AST.Function (mkVHDLExtId replaceId)  [ AST.IfaceVarDec vecPar vectorTM
                                          , AST.IfaceVarDec iPar   unsignedTM
                                          , AST.IfaceVarDec aPar   elemTM
                                          ] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-1);
    replaceVar =
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                                (AST.PrimLit "1"))   ]))
                Nothing
       --  res AST.:= vec(0 to i-1) & a & vec(i+1 to length'vec-1)
    replaceExpr1 = AST.NSimple resId AST.:= AST.PrimName (AST.NSimple vecPar)
    replaceExpr2 = AST.NIndexed (AST.IndexedName (AST.NSimple resId) [genExprFCall (mkVHDLBasicId toIntegerId) (AST.PrimName $ AST.NSimple $ iPar)]) AST.:= AST.PrimName (AST.NSimple aPar)
    replaceRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    vecSlice init last =  AST.PrimName (AST.NSlice 
                                        (AST.SliceName 
                                              (AST.NSimple vecPar) 
                                              (AST.ToRange init last)))
    lastSpec = AST.Function (mkVHDLExtId lastId) [AST.IfaceVarDec vecPar vectorTM] elemTM
       -- return vec(vec'length-1);
    lastExpr = AST.ReturnSm (Just $ (AST.PrimName $ AST.NIndexed (AST.IndexedName 
                    (AST.NSimple vecPar) 
                    [AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "1"])))
    initSpec = AST.Function (mkVHDLExtId initId) [AST.IfaceVarDec vecPar vectorTM] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-2);
    initVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                                (AST.PrimLit "2"))   ]))
                Nothing
       -- resAST.:= vec(0 to vec'length-2)
    initExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimLit "0") 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "2"))
    initRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    minimumSpec = AST.Function (mkVHDLExtId minimumId) [AST.IfaceVarDec leftPar   naturalTM,
                                   AST.IfaceVarDec rightPar naturalTM ] naturalTM
    minimumExpr = AST.IfSm ((AST.PrimName $ AST.NSimple leftPar) AST.:<: (AST.PrimName $ AST.NSimple rightPar))
                        [AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple leftPar)]
                        []
                        (Just $ AST.Else [minimumExprRet])
      where minimumExprRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple rightPar)
    takeSpec = AST.Function (mkVHDLExtId takeId) [AST.IfaceVarDec nPar   naturalTM,
                                   AST.IfaceVarDec vecPar vectorTM ] vectorTM
       -- variable res : fsvec_x (0 to (minimum (n,vec'length))-1);
    minLength = AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId minimumId))  
                              [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple nPar)
                              ,Nothing AST.:=>: AST.ADExpr (AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing))]
    takeVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                               (minLength AST.:-:
                                (AST.PrimLit "1"))   ]))
                Nothing
       -- res AST.:= vec(0 to n-1)
    takeExpr = AST.NSimple resId AST.:= 
                    (vecSlice (AST.PrimLit "0") 
                              (minLength AST.:-: AST.PrimLit "1"))
    takeRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    dropSpec = AST.Function (mkVHDLExtId dropId) [AST.IfaceVarDec nPar   naturalTM,
                                   AST.IfaceVarDec vecPar vectorTM ] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-n-1);
    dropVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                               (AST.PrimName $ AST.NSimple nPar)AST.:-: (AST.PrimLit "1")) ]))
               Nothing
       -- res AST.:= vec(n to vec'length-1)
    dropExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimName $ AST.NSimple nPar) 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "1"))
    dropRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    plusgtSpec = AST.Function (mkVHDLExtId plusgtId) [AST.IfaceVarDec aPar   elemTM,
                                       AST.IfaceVarDec vecPar vectorTM] vectorTM 
    -- variable res : fsvec_x (0 to vec'length);
    plusgtVar = 
      AST.VarDec resId 
             (AST.SubtypeIn vectorTM
               (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0")
                        (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing))]))
             Nothing
    plusgtExpr = AST.NSimple resId AST.:= 
                   ((AST.PrimName $ AST.NSimple aPar) AST.:&: 
                    (AST.PrimName $ AST.NSimple vecPar))
    plusgtRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    emptySpec = AST.Function (mkVHDLExtId emptyId) [] vectorTM
    emptyVar = 
          AST.VarDec resId
            (AST.SubtypeIn vectorTM
              (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0") (AST.PrimLit "-1")]))
             Nothing
    emptyExpr = AST.ReturnSm (Just $ AST.PrimName (AST.NSimple resId))
    singletonSpec = AST.Function (mkVHDLExtId singletonId) [AST.IfaceVarDec aPar elemTM ] 
                                         vectorTM
    -- variable res : fsvec_x (0 to 0) := (others => a);
    singletonVar = 
      AST.VarDec resId 
             (AST.SubtypeIn vectorTM
               (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0") (AST.PrimLit "0")]))
             (Just $ AST.Aggregate [AST.ElemAssoc (Just AST.Others) 
                                          (AST.PrimName $ AST.NSimple aPar)])
    singletonRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    copynSpec = AST.Function (mkVHDLExtId copynId) [AST.IfaceVarDec nPar   naturalTM,
                                   AST.IfaceVarDec aPar   elemTM   ] vectorTM 
    -- variable res : fsvec_x (0 to n-1) := (others => a);
    copynVar = 
      AST.VarDec resId 
             (AST.SubtypeIn vectorTM
               (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0")
                            ((AST.PrimName (AST.NSimple nPar)) AST.:-:
                             (AST.PrimLit "1"))   ]))
             (Just $ AST.Aggregate [AST.ElemAssoc (Just AST.Others) 
                                          (AST.PrimName $ AST.NSimple aPar)])
    -- return res
    copynExpr = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    selSpec = AST.Function (mkVHDLExtId selId) [AST.IfaceVarDec fPar   naturalTM,
                               AST.IfaceVarDec sPar   naturalTM,
                               AST.IfaceVarDec nPar   naturalTM,
                               AST.IfaceVarDec vecPar vectorTM ] vectorTM
    -- variable res : fsvec_x (0 to n-1);
    selVar = 
      AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                    [AST.ToRange (AST.PrimLit "0")
                      ((AST.PrimName (AST.NSimple nPar)) AST.:-:
                      (AST.PrimLit "1"))   ])
                )
                Nothing
    -- for i res'range loop
    --   res(i) := vec(f+i*s);
    -- end loop;
    selFor = AST.ForSM iId (AST.AttribRange $ AST.AttribName (AST.NSimple resId) (AST.NSimple $ rangeId) Nothing) [selAssign]
    -- res(i) := vec(f+i*s);
    selAssign = let origExp = AST.PrimName (AST.NSimple fPar) AST.:+: 
                                (AST.PrimName (AST.NSimple iId) AST.:*: 
                                  AST.PrimName (AST.NSimple sPar)) in
                                  AST.NIndexed (AST.IndexedName (AST.NSimple resId) [AST.PrimName (AST.NSimple iId)]) AST.:=
                                    (AST.PrimName $ AST.NIndexed (AST.IndexedName (AST.NSimple vecPar) [origExp]))
    -- return res;
    selRet =  AST.ReturnSm (Just $ AST.PrimName (AST.NSimple resId))
    ltplusSpec = AST.Function (mkVHDLExtId ltplusId) [AST.IfaceVarDec vecPar vectorTM,
                                        AST.IfaceVarDec aPar   elemTM] vectorTM 
     -- variable res : fsvec_x (0 to vec'length);
    ltplusVar = 
      AST.VarDec resId 
        (AST.SubtypeIn vectorTM
          (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
            [AST.ToRange (AST.PrimLit "0")
              (AST.PrimName (AST.NAttribute $ 
                AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing))]))
        Nothing
    ltplusExpr = AST.NSimple resId AST.:= 
                     ((AST.PrimName $ AST.NSimple vecPar) AST.:&: 
                      (AST.PrimName $ AST.NSimple aPar))
    ltplusRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    plusplusSpec = AST.Function (mkVHDLExtId plusplusId) [AST.IfaceVarDec vec1Par vectorTM,
                                             AST.IfaceVarDec vec2Par vectorTM] 
                                             vectorTM 
    -- variable res : fsvec_x (0 to vec1'length + vec2'length -1);
    plusplusVar = 
      AST.VarDec resId 
        (AST.SubtypeIn vectorTM
          (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
            [AST.ToRange (AST.PrimLit "0")
              (AST.PrimName (AST.NAttribute $ 
                AST.AttribName (AST.NSimple vec1Par) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:+:
                  AST.PrimName (AST.NAttribute $ 
                AST.AttribName (AST.NSimple vec2Par) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                  AST.PrimLit "1")]))
       Nothing
    plusplusExpr = AST.NSimple resId AST.:= 
                     ((AST.PrimName $ AST.NSimple vec1Par) AST.:&: 
                      (AST.PrimName $ AST.NSimple vec2Par))
    plusplusRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    lengthTSpec = AST.Function (mkVHDLExtId lengthTId) [AST.IfaceVarDec vecPar vectorTM] naturalTM
    lengthTExpr = AST.ReturnSm (Just $ AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing))
    shiftlSpec = AST.Function (mkVHDLExtId shiftlId) [AST.IfaceVarDec vecPar vectorTM,
                                   AST.IfaceVarDec aPar   elemTM  ] vectorTM 
    -- variable res : fsvec_x (0 to vec'length-1);
    shiftlVar = 
     AST.VarDec resId 
            (AST.SubtypeIn vectorTM
              (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
               [AST.ToRange (AST.PrimLit "0")
                        (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                           (AST.PrimLit "1")) ]))
            Nothing
    -- res := a & init(vec)
    shiftlExpr = AST.NSimple resId AST.:=
                    (AST.PrimName (AST.NSimple aPar) AST.:&:
                     (AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId initId))  
                       [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)]))
    shiftlRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)       
    shiftrSpec = AST.Function (mkVHDLExtId shiftrId) [AST.IfaceVarDec vecPar vectorTM,
                                       AST.IfaceVarDec aPar   elemTM  ] vectorTM 
    -- variable res : fsvec_x (0 to vec'length-1);
    shiftrVar = 
     AST.VarDec resId 
            (AST.SubtypeIn vectorTM
              (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
               [AST.ToRange (AST.PrimLit "0")
                        (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                           (AST.PrimLit "1")) ]))
            Nothing
    -- res := tail(vec) & a
    shiftrExpr = AST.NSimple resId AST.:=
                  ((AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId tailId))  
                    [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)]) AST.:&:
                  (AST.PrimName (AST.NSimple aPar)))
                
    shiftrRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)      
    nullSpec = AST.Function (mkVHDLExtId nullId) [AST.IfaceVarDec vecPar vectorTM] booleanTM
    -- return vec'length = 0
    nullExpr = AST.ReturnSm (Just $ 
                AST.PrimName (AST.NAttribute $ 
                  AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:=:
                    AST.PrimLit "0")
    rotlSpec = AST.Function (mkVHDLExtId rotlId) [AST.IfaceVarDec vecPar vectorTM] vectorTM 
    -- variable res : fsvec_x (0 to vec'length-1);
    rotlVar = 
     AST.VarDec resId 
            (AST.SubtypeIn vectorTM
              (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
               [AST.ToRange (AST.PrimLit "0")
                        (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                           (AST.PrimLit "1")) ]))
            Nothing
    -- if null(vec) then res := vec else res := last(vec) & init(vec)
    rotlExpr = AST.IfSm (AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId nullId))  
                          [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)])
                        [AST.NSimple resId AST.:= (AST.PrimName $ AST.NSimple vecPar)]
                        []
                        (Just $ AST.Else [rotlExprRet])
      where rotlExprRet = 
                AST.NSimple resId AST.:= 
                      ((AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId lastId))  
                        [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)]) AST.:&:
                      (AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId initId))  
                        [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)]))
    rotlRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)       
    rotrSpec = AST.Function (mkVHDLExtId rotrId) [AST.IfaceVarDec vecPar vectorTM] vectorTM 
    -- variable res : fsvec_x (0 to vec'length-1);
    rotrVar = 
     AST.VarDec resId 
            (AST.SubtypeIn vectorTM
              (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
               [AST.ToRange (AST.PrimLit "0")
                        (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                           (AST.PrimLit "1")) ]))
            Nothing
    -- if null(vec) then res := vec else res := tail(vec) & head(vec)
    rotrExpr = AST.IfSm (AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId nullId))  
                          [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)])
                        [AST.NSimple resId AST.:= (AST.PrimName $ AST.NSimple vecPar)]
                        []
                        (Just $ AST.Else [rotrExprRet])
      where rotrExprRet = 
                AST.NSimple resId AST.:= 
                      ((AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId tailId))  
                        [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)]) AST.:&:
                      (AST.PrimFCall $ AST.FCall (AST.NSimple (mkVHDLExtId headId))  
                        [Nothing AST.:=>: AST.ADExpr (AST.PrimName $ AST.NSimple vecPar)]))
    rotrRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    reverseSpec = AST.Function (mkVHDLExtId reverseId) [AST.IfaceVarDec vecPar vectorTM] vectorTM
    reverseVar = 
      AST.VarDec resId 
             (AST.SubtypeIn vectorTM
               (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0")
                         (AST.PrimName (AST.NAttribute $ 
                           AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                            (AST.PrimLit "1")) ]))
             Nothing
    -- for i in 0 to res'range loop
    --   res(vec'length-i-1) := vec(i);
    -- end loop;
    reverseFor = 
       AST.ForSM iId (AST.AttribRange $ AST.AttribName (AST.NSimple resId) (AST.NSimple $ rangeId) Nothing) [reverseAssign]
    -- res(vec'length-i-1) := vec(i);
    reverseAssign = AST.NIndexed (AST.IndexedName (AST.NSimple resId) [destExp]) AST.:=
      (AST.PrimName $ AST.NIndexed (AST.IndexedName (AST.NSimple vecPar) 
                           [AST.PrimName $ AST.NSimple iId]))
        where destExp = AST.PrimName (AST.NAttribute $ AST.AttribName (AST.NSimple vecPar) 
                                   (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-: 
                        AST.PrimName (AST.NSimple iId) AST.:-: 
                        (AST.PrimLit "1") 
    -- return res;
    reverseRet = AST.ReturnSm (Just $ AST.PrimName (AST.NSimple resId))

    
-----------------------------------------------------------------------------
-- A table of builtin functions
-----------------------------------------------------------------------------

-- A function that generates VHDL for a builtin function
type BuiltinBuilder = 
  (Either CoreSyn.CoreBndr AST.VHDLName) -- ^ The destination signal and it's original type
  -> CoreSyn.CoreBndr -- ^ The function called
  -> [Either CoreSyn.CoreExpr AST.Expr] -- ^ The value arguments passed (excluding type and
                    --   dictionary arguments).
  -> TranslatorSession ([AST.ConcSm], [CoreSyn.CoreBndr]) 
  -- ^ The corresponding VHDL concurrent statements and entities
  --   instantiated.

-- A map of a builtin function to VHDL function builder 
type NameTable = Map.Map String (Int, BuiltinBuilder )

-- | The builtin functions we support. Maps a name to an argument count and a
-- builder function.
globalNameTable :: NameTable
globalNameTable = Map.fromList
  [ (exId             , (2, genFCall True          ) )
  , (replaceId        , (3, genFCall False          ) )
  , (headId           , (1, genFCall True           ) )
  , (lastId           , (1, genFCall True           ) )
  , (tailId           , (1, genFCall False          ) )
  , (initId           , (1, genFCall False          ) )
  , (takeId           , (2, genFCall False          ) )
  , (dropId           , (2, genFCall False          ) )
  , (selId            , (4, genFCall False          ) )
  , (plusgtId         , (2, genFCall False          ) )
  , (ltplusId         , (2, genFCall False          ) )
  , (plusplusId       , (2, genFCall False          ) )
  , (mapId            , (2, genMap                  ) )
  , (zipWithId        , (3, genZipWith              ) )
  , (foldlId          , (3, genFoldl                ) )
  , (foldrId          , (3, genFoldr                ) )
  , (zipId            , (2, genZip                  ) )
  , (unzipId          , (1, genUnzip                ) )
  , (shiftlId         , (2, genFCall False          ) )
  , (shiftrId         , (2, genFCall False          ) )
  , (rotlId           , (1, genFCall False          ) )
  , (rotrId           , (1, genFCall False          ) )
  , (concatId         , (1, genConcat               ) )
  , (reverseId        , (1, genFCall False          ) )
  , (iteratenId       , (3, genIteraten             ) )
  , (iterateId        , (2, genIterate              ) )
  , (generatenId      , (3, genGeneraten            ) )
  , (generateId       , (2, genGenerate             ) )
  , (emptyId          , (0, genFCall False          ) )
  , (singletonId      , (1, genFCall False          ) )
  , (copynId          , (2, genFCall False          ) )
  , (copyId           , (1, genCopy                 ) )
  , (lengthTId        , (1, genFCall False          ) )
  , (nullId           , (1, genFCall False          ) )
  , (hwxorId          , (2, genOperator2 AST.Xor    ) )
  , (hwandId          , (2, genOperator2 AST.And    ) )
  , (hworId           , (2, genOperator2 AST.Or     ) )
  , (hwnotId          , (1, genOperator1 AST.Not    ) )
  , (equalityId       , (2, genOperator2 (AST.:=:)  ) )
  , (inEqualityId     , (2, genOperator2 (AST.:/=:) ) )
  , (ltId             , (2, genOperator2 (AST.:<:)  ) )
  , (lteqId           , (2, genOperator2 (AST.:<=:) ) )
  , (gtId             , (2, genOperator2 (AST.:>:)  ) )
  , (gteqId           , (2, genOperator2 (AST.:>=:) ) )
  , (boolOrId         , (2, genOperator2 AST.Or     ) )
  , (boolAndId        , (2, genOperator2 AST.And    ) )
  , (plusId           , (2, genOperator2 (AST.:+:)  ) )
  , (timesId          , (2, genOperator2 (AST.:*:)  ) )
  , (negateId         , (1, genNegation             ) )
  , (minusId          , (2, genOperator2 (AST.:-:)  ) )
  , (fromSizedWordId  , (1, genFromSizedWord        ) )
  , (fromIntegerId    , (1, genFromInteger          ) )
  , (resizeId         , (1, genResize               ) )
  , (sizedIntId       , (1, genSizedInt             ) )
  , (smallIntegerId   , (1, genFromInteger          ) )
  , (fstId            , (1, genFst                  ) )
  , (sndId            , (1, genSnd                  ) )
  , (blockRAMId       , (5, genBlockRAM             ) )
  --, (tfvecId          , (1, genTFVec                ) )
  , (minimumId        , (2, error $ "\nFunction name: \"minimum\" is used internally, use another name"))
  ]
