module Generate where

-- Standard modules
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Maybe
import qualified Data.Either as Either
import Data.Accessor
import Debug.Trace

-- ForSyDe
import qualified ForSyDe.Backend.VHDL.AST as AST

-- GHC API
import CoreSyn
import Type
import qualified Var
import qualified IdInfo

-- Local imports
import Constants
import VHDLTypes
import VHDLTools
import CoreTools
import Pretty

-----------------------------------------------------------------------------
-- Functions to generate VHDL for builtin functions
-----------------------------------------------------------------------------

-- | A function to wrap a builder-like function that expects its arguments to
-- be expressions.
genExprArgs ::
  (dst -> func -> [AST.Expr] -> res)
  -> (dst -> func -> [Either CoreSyn.CoreExpr AST.Expr] -> res)
genExprArgs wrap dst func args = wrap dst func args'
  where args' = map (either (varToVHDLExpr.exprToVar) id) args
  
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

-- | A function to wrap a builder-like function that produces an expression
-- and expects it to be assigned to the destination.
genExprRes ::
  ((Either CoreSyn.CoreBndr AST.VHDLName) -> func -> [arg] -> VHDLSession AST.Expr)
  -> ((Either CoreSyn.CoreBndr AST.VHDLName) -> func -> [arg] -> VHDLSession [AST.ConcSm])
genExprRes wrap dst func args = do
  expr <- wrap dst func args
  return $ [mkUncondAssign dst expr]

-- | Generate a binary operator application. The first argument should be a
-- constructor from the AST.Expr type, e.g. AST.And.
genOperator2 :: (AST.Expr -> AST.Expr -> AST.Expr) -> BuiltinBuilder 
genOperator2 op = genExprArgs $ genExprRes (genOperator2' op)
genOperator2' :: (AST.Expr -> AST.Expr -> AST.Expr) -> dst -> CoreSyn.CoreBndr -> [AST.Expr] -> VHDLSession AST.Expr
genOperator2' op _ f [arg1, arg2] = return $ op arg1 arg2

-- | Generate a unary operator application
genOperator1 :: (AST.Expr -> AST.Expr) -> BuiltinBuilder 
genOperator1 op = genExprArgs $ genExprRes (genOperator1' op)
genOperator1' :: (AST.Expr -> AST.Expr) -> dst -> CoreSyn.CoreBndr -> [AST.Expr] -> VHDLSession AST.Expr
genOperator1' op _ f [arg] = return $ op arg

-- | Generate a function call from the destination binder, function name and a
-- list of expressions (its arguments)
genFCall :: BuiltinBuilder 
genFCall = genExprArgs $ genExprRes genFCall'
genFCall' :: Either CoreSyn.CoreBndr AST.VHDLName -> CoreSyn.CoreBndr -> [AST.Expr] -> VHDLSession AST.Expr
genFCall' (Left res) f args = do
  let fname = varToString f
  let el_ty = (tfvec_elem . Var.varType) res
  id <- vectorFunId el_ty fname
  return $ AST.PrimFCall $ AST.FCall (AST.NSimple id)  $
             map (\exp -> Nothing AST.:=>: AST.ADExpr exp) args
genFCall' (Right name) _ _ = error $ "Cannot generate builtin function call assigned to a VHDLName: " ++ show name

-- | Generate a generate statement for the builtin function "map"
genMap :: BuiltinBuilder
genMap = genVarArgs genMap'
genMap' (Left res) f [mapped_f, arg] = do
  signatures <- getA vsSignatures
  let entity = Maybe.fromMaybe
        (error $ "Using function '" ++ (varToString mapped_f) ++ "' without signature? This should not happen!") 
        (Map.lookup mapped_f signatures)
  let
    -- Setup the generate scheme
    len         = (tfvec_len . Var.varType) res
    -- TODO: Use something better than varToString
    label       = mkVHDLExtId ("mapVector" ++ (varToString res))
    nPar        = AST.unsafeVHDLBasicId "n"
    range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
    genScheme   = AST.ForGn nPar range
    -- Get the entity name and port names
    entity_id   = ent_id entity
    argports   = map fst (ent_args entity)
    resport     = fst (ent_res entity)
    -- Assign the ports
    inport      = mkAssocElemIndexed (argports!!0) (varToVHDLId arg) nPar
    outport     = mkAssocElemIndexed resport (varToVHDLId res) nPar
    portassigns = [inport,outport]
    -- Generate the portmap
    mapLabel    = "map" ++ (AST.fromVHDLId entity_id)
    compins     = mkComponentInst mapLabel entity_id portassigns
    -- Return the generate functions
    genSm       = AST.CSGSm $ AST.GenerateSm label genScheme [] [compins]
    in
      return $ [genSm]
genMap' (Right name) _ _ = error $ "Cannot generate map function call assigned to a VHDLName: " ++ show name
    
genZipWith :: BuiltinBuilder
genZipWith = genVarArgs genZipWith'
genZipWith' :: (Either CoreSyn.CoreBndr AST.VHDLName) -> CoreSyn.CoreBndr -> [Var.Var] -> VHDLSession [AST.ConcSm]
genZipWith' (Left res) f args@[zipped_f, arg1, arg2] = do
  signatures <- getA vsSignatures
  let entity = Maybe.fromMaybe
        (error $ "Using function '" ++ (varToString zipped_f) ++ "' without signature? This should not happen!") 
        (Map.lookup zipped_f signatures)
  let
    -- Setup the generate scheme
    len         = (tfvec_len . Var.varType) res
    -- TODO: Use something better than varToString
    label       = mkVHDLExtId ("zipWithVector" ++ (varToString res))
    nPar        = AST.unsafeVHDLBasicId "n"
    range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
    genScheme   = AST.ForGn nPar range
    -- Get the entity name and port names
    entity_id   = ent_id entity
    argports    = map fst (ent_args entity)
    resport     = fst (ent_res entity)
    -- Assign the ports
    inport1     = mkAssocElemIndexed (argports!!0) (varToVHDLId arg1) nPar
    inport2     = mkAssocElemIndexed (argports!!1) (varToVHDLId arg2) nPar 
    outport     = mkAssocElemIndexed resport (varToVHDLId res) nPar
    portassigns = [inport1,inport2,outport]
    -- Generate the portmap
    mapLabel    = "zipWith" ++ (AST.fromVHDLId entity_id)
    compins     = mkComponentInst mapLabel entity_id portassigns
    -- Return the generate functions
    genSm       = AST.CSGSm $ AST.GenerateSm label genScheme [] [compins]
    in
      return $ [genSm]
{-
genFoldl :: BuiltinBuilder
genFoldl = genVarArgs genFoldl'
genFoldl' resVal f [folded_f, startVal, inVec] = do
  signatures <- getA vsSignatures
  let entity = Maybe.fromMaybe
        (error $ "Using function '" ++ (varToString folded_f) ++ "' without signature? This should not happen!") 
        (Map.lookup folded_f signatures)
  let (vec, _) = splitAppTy (Var.varType inVec)
  let vecty = Type.mkAppTy vec (Var.varType startVal)
  vecType <- vhdl_ty vecty
  -- Setup the generate scheme
  let  len         = (tfvec_len . Var.varType) inVec
  let  genlabel       = mkVHDLExtId ("foldlVector" ++ (varToString inVec))
  let  blockLabel  = mkVHDLExtId ("foldlVector" ++ (varToString startVal))
  let  range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
  let  genScheme   = AST.ForGn (AST.unsafeVHDLBasicId "n") range
  -- Make the intermediate vector
  let  tmpVec      = AST.BDISD $ AST.SigDec (mkVHDLExtId "tmp") vecType Nothing
  -- Get the entity name and port names
  let entity_id   = ent_id entity
  let argports    = map (Monad.liftM fst) (ent_args entity)
  let resport     = (Monad.liftM fst) (ent_res entity)
  -- Return the generate functions
  let genSm       = AST.GenerateSm genlabel genScheme [] 
                      [ AST.CSGSm (genFirstCell (entity_id, argports, resport) 
                                    [startVal, inVec, resVal])
                      , AST.CSGSm (genOtherCell (entity_id, argports, resport) 
                                    [startVal, inVec, resVal])
                      , AST.CSGSm (genLastCell (entity_id, argports, resport) 
                                    [startVal, inVec, resVal])
                      ]
  return $ [AST.CSBSm $ AST.BlockSm blockLabel [] (AST.PMapAspect []) [tmpVec] [AST.CSGSm genSm]]
  where
    genFirstCell (entity_id, argports, resport) [startVal, inVec, resVal] = cellGn
      where
        cellLabel    = mkVHDLExtId "firstcell"
        cellGenScheme = AST.IfGn ((AST.PrimName $ AST.NSimple nPar)  AST.:=: (AST.PrimLit "0"))
        tmpId       = mkVHDLExtId "tmp"
        nPar        = AST.unsafeVHDLBasicId "n"
        -- Assign the ports
        inport1     = mkAssocElem (argports!!0) (varToString startVal)
        inport2     = mkAssocElemIndexed (argports!!1) (varToVHDLId inVec) nPar 
        outport     = mkAssocElemIndexed resport tmpId nPar
        portassigns = Maybe.catMaybes [inport1,inport2,outport]
        -- Generate the portmap
        mapLabel    = "cell" ++ (AST.fromVHDLId entity_id)
        compins     = mkComponentInst mapLabel entity_id portassigns
        -- Return the generate functions
        cellGn       = AST.GenerateSm cellLabel cellGenScheme [] [compins]
    genOtherCell (entity_id, argports, resport) [startVal, inVec, resVal] = cellGn
      where
        len         = (tfvec_len . Var.varType) inVec
        cellLabel    = mkVHDLExtId "othercell"
        cellGenScheme = AST.IfGn $ AST.And ((AST.PrimName $ AST.NSimple nPar)  AST.:>: (AST.PrimLit "0"))
                                ((AST.PrimName $ AST.NSimple nPar)  AST.:<: (AST.PrimLit $ show (len-1)))
        tmpId       = mkVHDLExtId "tmp"
        nPar        = AST.unsafeVHDLBasicId "n"
        -- Assign the ports
        inport1     = mkAssocElemIndexed (argports!!0) tmpId (AST.unsafeVHDLBasicId "n-1")
        inport2     = mkAssocElemIndexed (argports!!1) (varToVHDLId inVec) nPar 
        outport     = mkAssocElemIndexed resport tmpId nPar
        portassigns = Maybe.catMaybes [inport1,inport2,outport]
        -- Generate the portmap
        mapLabel    = "cell" ++ (AST.fromVHDLId entity_id)
        compins     = mkComponentInst mapLabel entity_id portassigns
        -- Return the generate functions
        cellGn      = AST.GenerateSm cellLabel cellGenScheme [] [compins]
    genLastCell (entity_id, argports, resport) [startVal, inVec, resVal] = cellGn
      where
        len         = (tfvec_len . Var.varType) inVec
        cellLabel    = mkVHDLExtId "lastCell"
        cellGenScheme = AST.IfGn ((AST.PrimName $ AST.NSimple nPar)  AST.:=: (AST.PrimLit $ show (len-1)))
        tmpId       = mkVHDLExtId "tmp"
        nPar        = AST.unsafeVHDLBasicId "n"
        -- Assign the ports
        inport1     = mkAssocElemIndexed (argports!!0) tmpId (AST.unsafeVHDLBasicId "n-1")
        inport2     = mkAssocElemIndexed (argports!!1) (varToVHDLId inVec) nPar 
        outport     = mkAssocElemIndexed resport tmpId nPar
        portassigns = Maybe.catMaybes [inport1,inport2,outport]
        -- Generate the portmap
        mapLabel    = "cell" ++ (AST.fromVHDLId entity_id)
        compins     = mkComponentInst mapLabel entity_id portassigns
        -- Generate the output assignment
        assign      = mkUncondAssign (Left resVal) (AST.PrimName (AST.NIndexed (AST.IndexedName 
                              (AST.NSimple tmpId) [AST.PrimLit $ show (len-1)])))
        -- Return the generate functions
        cellGn      = AST.GenerateSm cellLabel cellGenScheme [] [compins,assign]
-}
-----------------------------------------------------------------------------
-- Function to generate VHDL for applications
-----------------------------------------------------------------------------
genApplication ::
  (Either CoreSyn.CoreBndr AST.VHDLName) -- ^ Where to store the result?
  -> CoreSyn.CoreBndr -- ^ The function to apply
  -> [Either CoreSyn.CoreExpr AST.Expr] -- ^ The arguments to apply
  -> VHDLSession [AST.ConcSm] -- ^ The resulting concurrent statements
genApplication dst f args =
  case Var.globalIdVarDetails f of
    IdInfo.DataConWorkId dc -> case dst of
      -- It's a datacon. Create a record from its arguments.
      Left bndr -> do
        -- We have the bndr, so we can get at the type
        labels <- getFieldLabels (Var.varType bndr)
        return $ zipWith mkassign labels $ map (either exprToVHDLExpr id) args
        where
          mkassign :: AST.VHDLId -> AST.Expr -> AST.ConcSm
          mkassign label arg =
            let sel_name = mkSelectedName ((either varToVHDLName id) dst) label in
            mkUncondAssign (Right sel_name) arg
      Right _ -> error $ "Generate.genApplication Can't generate dataconstructor application without an original binder"
    IdInfo.VanillaGlobal -> do
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
            error $ "Generate.genApplication Incorrect number of arguments to builtin function: " ++ pprString f ++ " Args: " ++ show args
        Nothing -> error $ "Using function from another module that is not a known builtin: " ++ pprString f
    IdInfo.NotGlobalId -> do
      signatures <- getA vsSignatures
      -- This is a local id, so it should be a function whose definition we
      -- have and which can be turned into a component instantiation.
      let  
        signature = Maybe.fromMaybe 
          (error $ "Using function '" ++ (varToString f) ++ "' without signature? This should not happen!") 
          (Map.lookup f signatures)
        entity_id = ent_id signature
        -- TODO: Using show here isn't really pretty, but we'll need some
        -- unique-ish value...
        label = "comp_ins_" ++ (either show show) dst
        portmaps = mkAssocElems (map (either exprToVHDLExpr id) args) ((either varToVHDLName id) dst) signature
        in
          return [mkComponentInst label entity_id portmaps]
    details -> error $ "Calling unsupported function " ++ pprString f ++ " with GlobalIdDetails " ++ pprString details

-----------------------------------------------------------------------------
-- Functions to generate functions dealing with vectors.
-----------------------------------------------------------------------------

-- Returns the VHDLId of the vector function with the given name for the given
-- element type. Generates -- this function if needed.
vectorFunId :: Type.Type -> String -> VHDLSession AST.VHDLId
vectorFunId el_ty fname = do
  elemTM <- vhdl_ty el_ty
  -- TODO: This should not be duplicated from mk_vector_ty. Probably but it in
  -- the VHDLState or something.
  let vectorTM = mkVHDLExtId $ "vector_" ++ (AST.fromVHDLId elemTM)
  typefuns <- getA vsTypeFuns
  case Map.lookup (OrdType el_ty, fname) typefuns of
    -- Function already generated, just return it
    Just (id, _) -> return id
    -- Function not generated yet, generate it
    Nothing -> do
      let functions = genUnconsVectorFuns elemTM vectorTM
      case lookup fname functions of
        Just body -> do
          modA vsTypeFuns $ Map.insert (OrdType el_ty, fname) (function_id, body)
          return function_id
        Nothing -> error $ "I don't know how to generate vector function " ++ fname
  where
    function_id = mkVHDLExtId fname

genUnconsVectorFuns :: AST.TypeMark -- ^ type of the vector elements
                    -> AST.TypeMark -- ^ type of the vector
                    -> [(String, AST.SubProgBody)]
genUnconsVectorFuns elemTM vectorTM  = 
  [ (exId, AST.SubProgBody exSpec      []                  [exExpr])
  , (replaceId, AST.SubProgBody replaceSpec [AST.SPVD replaceVar] [replaceExpr,replaceRet])
  , (headId, AST.SubProgBody headSpec    []                  [headExpr])
  , (lastId, AST.SubProgBody lastSpec    []                  [lastExpr])
  , (initId, AST.SubProgBody initSpec    [AST.SPVD initVar]  [initExpr, initRet])
  , (tailId, AST.SubProgBody tailSpec    [AST.SPVD tailVar]  [tailExpr, tailRet])
  , (takeId, AST.SubProgBody takeSpec    [AST.SPVD takeVar]  [takeExpr, takeRet])
  , (dropId, AST.SubProgBody dropSpec    [AST.SPVD dropVar]  [dropExpr, dropRet])
  , (plusgtId, AST.SubProgBody plusgtSpec  [AST.SPVD plusgtVar] [plusgtExpr, plusgtRet])
  , (emptyId, AST.SubProgBody emptySpec   [AST.SPCD emptyVar] [emptyExpr])
  , (singletonId, AST.SubProgBody singletonSpec [AST.SPVD singletonVar] [singletonRet])
  , (copyId, AST.SubProgBody copySpec    [AST.SPVD copyVar]      [copyExpr])
  ]
  where 
    ixPar   = AST.unsafeVHDLBasicId "ix"
    vecPar  = AST.unsafeVHDLBasicId "vec"
    nPar    = AST.unsafeVHDLBasicId "n"
    iId     = AST.unsafeVHDLBasicId "i"
    iPar    = iId
    aPar    = AST.unsafeVHDLBasicId "a"
    resId   = AST.unsafeVHDLBasicId "res"
    exSpec = AST.Function (mkVHDLExtId exId) [AST.IfaceVarDec vecPar vectorTM,
                               AST.IfaceVarDec ixPar  naturalTM] elemTM
    exExpr = AST.ReturnSm (Just $ AST.PrimName $ AST.NIndexed 
              (AST.IndexedName (AST.NSimple vecPar) [AST.PrimName $ 
                AST.NSimple ixPar]))
    replaceSpec = AST.Function (mkVHDLExtId replaceId)  [ AST.IfaceVarDec vecPar vectorTM
                                          , AST.IfaceVarDec iPar   naturalTM
                                          , AST.IfaceVarDec aPar   elemTM
                                          ] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-1);
    replaceVar =
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) AST.:-:
                                (AST.PrimLit "1"))   ]))
                Nothing
       --  res AST.:= vec(0 to i-1) & a & vec(i+1 to length'vec-1)
    replaceExpr = AST.NSimple resId AST.:=
           (vecSlice (AST.PrimLit "0") (AST.PrimName (AST.NSimple iPar) AST.:-: AST.PrimLit "1") AST.:&:
            AST.PrimName (AST.NSimple aPar) AST.:&: 
             vecSlice (AST.PrimName (AST.NSimple iPar) AST.:+: AST.PrimLit "1")
                      ((AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing)) 
                                                              AST.:-: AST.PrimLit "1"))
    replaceRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    vecSlice init last =  AST.PrimName (AST.NSlice 
                                        (AST.SliceName 
                                              (AST.NSimple vecPar) 
                                              (AST.ToRange init last)))
    headSpec = AST.Function (mkVHDLExtId headId) [AST.IfaceVarDec vecPar vectorTM] elemTM
       -- return vec(0);
    headExpr = AST.ReturnSm (Just $ (AST.PrimName $ AST.NIndexed (AST.IndexedName 
                    (AST.NSimple vecPar) [AST.PrimLit "0"])))
    lastSpec = AST.Function (mkVHDLExtId lastId) [AST.IfaceVarDec vecPar vectorTM] elemTM
       -- return vec(vec'length-1);
    lastExpr = AST.ReturnSm (Just $ (AST.PrimName $ AST.NIndexed (AST.IndexedName 
                    (AST.NSimple vecPar) 
                    [AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "1"])))
    initSpec = AST.Function (mkVHDLExtId initId) [AST.IfaceVarDec vecPar vectorTM] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-2);
    initVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) AST.:-:
                                (AST.PrimLit "2"))   ]))
                Nothing
       -- resAST.:= vec(0 to vec'length-2)
    initExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimLit "0") 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "2"))
    initRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    tailSpec = AST.Function (mkVHDLExtId tailId) [AST.IfaceVarDec vecPar vectorTM] vectorTM
       -- variable res : fsvec_x (0 to vec'length-2); 
    tailVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) AST.:-:
                                (AST.PrimLit "2"))   ]))
                Nothing       
       -- res AST.:= vec(1 to vec'length-1)
    tailExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimLit "1") 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "1"))
    tailRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    takeSpec = AST.Function (mkVHDLExtId takeId) [AST.IfaceVarDec nPar   naturalTM,
                                   AST.IfaceVarDec vecPar vectorTM ] vectorTM
       -- variable res : fsvec_x (0 to n-1);
    takeVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                               ((AST.PrimName (AST.NSimple nPar)) AST.:-:
                                (AST.PrimLit "1"))   ]))
                Nothing
       -- res AST.:= vec(0 to n-1)
    takeExpr = AST.NSimple resId AST.:= 
                    (vecSlice (AST.PrimLit "1") 
                              (AST.PrimName (AST.NSimple $ nPar) AST.:-: AST.PrimLit "1"))
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
                              AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) AST.:-:
                               (AST.PrimName $ AST.NSimple nPar)AST.:-: (AST.PrimLit "1")) ]))
               Nothing
       -- res AST.:= vec(n to vec'length-1)
    dropExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimName $ AST.NSimple nPar) 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing) 
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
                          AST.AttribName (AST.NSimple vecPar) (mkVHDLBasicId lengthId) Nothing))]))
             Nothing
    plusgtExpr = AST.NSimple resId AST.:= 
                   ((AST.PrimName $ AST.NSimple aPar) AST.:&: 
                    (AST.PrimName $ AST.NSimple vecPar))
    plusgtRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    emptySpec = AST.Function (mkVHDLExtId emptyId) [] vectorTM
    emptyVar = 
          AST.ConstDec resId 
              (AST.SubtypeIn vectorTM Nothing)
              (Just $ AST.PrimLit "\"\"")
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
    copySpec = AST.Function (mkVHDLExtId copyId) [AST.IfaceVarDec nPar   naturalTM,
                                   AST.IfaceVarDec aPar   elemTM   ] vectorTM 
    -- variable res : fsvec_x (0 to n-1) := (others => a);
    copyVar = 
      AST.VarDec resId 
             (AST.SubtypeIn vectorTM
               (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0")
                            ((AST.PrimName (AST.NSimple nPar)) AST.:-:
                             (AST.PrimLit "1"))   ]))
             (Just $ AST.Aggregate [AST.ElemAssoc (Just AST.Others) 
                                          (AST.PrimName $ AST.NSimple aPar)])
    -- return res
    copyExpr = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)

-----------------------------------------------------------------------------
-- A table of builtin functions
-----------------------------------------------------------------------------

-- | The builtin functions we support. Maps a name to an argument count and a
-- builder function.
globalNameTable :: NameTable
globalNameTable = Map.fromList
  [ (exId             , (2, genFCall                ) )
  , (replaceId        , (3, genFCall                ) )
  , (headId           , (1, genFCall                ) )
  , (lastId           , (1, genFCall                ) )
  , (tailId           , (1, genFCall                ) )
  , (initId           , (1, genFCall                ) )
  , (takeId           , (2, genFCall                ) )
  , (dropId           , (2, genFCall                ) )
  , (plusgtId         , (2, genFCall                ) )
  , (mapId            , (2, genMap                  ) )
  , (zipWithId        , (3, genZipWith              ) )
  --, (foldlId          , (3, genFoldl                ) )
  , (emptyId          , (0, genFCall                ) )
  , (singletonId      , (1, genFCall                ) )
  , (copyId           , (2, genFCall                ) )
  , (hwxorId          , (2, genOperator2 AST.Xor    ) )
  , (hwandId          , (2, genOperator2 AST.And    ) )
  , (hworId           , (2, genOperator2 AST.Or     ) )
  , (hwnotId          , (1, genOperator1 AST.Not    ) )
  ]
