module Generate where

-- Standard modules
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Maybe
import Data.Accessor

-- ForSyDe
import qualified ForSyDe.Backend.VHDL.AST as AST

-- GHC API
import CoreSyn
import Type
import qualified Var

-- Local imports
import Constants
import VHDLTypes
import VHDLTools
import CoreTools

-- | Generate a binary operator application. The first argument should be a
-- constructor from the AST.Expr type, e.g. AST.And.
genExprOp2 :: (AST.Expr -> AST.Expr -> AST.Expr) -> CoreSyn.CoreBndr -> [AST.Expr] -> VHDLSession AST.Expr
genExprOp2 op res [arg1, arg2] = return $ op arg1 arg2

-- | Generate a unary operator application
genExprOp1 :: (AST.Expr -> AST.Expr) -> CoreSyn.CoreBndr -> [AST.Expr] -> VHDLSession AST.Expr
genExprOp1 op res [arg] = return $ op arg

-- | Generate a function call from the destination binder, function name and a
-- list of expressions (its arguments)
genExprFCall :: String -> CoreSyn.CoreBndr -> [AST.Expr] -> VHDLSession AST.Expr
genExprFCall fname res args = do
  let el_ty = (tfvec_elem . Var.varType) res
  id <- vectorFunId el_ty fname
  return $ AST.PrimFCall $ AST.FCall (AST.NSimple id)  $
             map (\exp -> Nothing AST.:=>: AST.ADExpr exp) args

-- | Generate a generate statement for the builtin function "map"
genMapCall :: 
  Entity -- | The entity to map
  -> [CoreSyn.CoreBndr] -- | The vectors
  -> VHDLSession AST.ConcSm -- | The resulting generate statement
genMapCall entity [arg, res] = return $ genSm
  where
    -- Setup the generate scheme
    len         = (tfvec_len . Var.varType) res
    label       = mkVHDLExtId ("mapVector" ++ (varToString res))
    nPar        = AST.unsafeVHDLBasicId "n"
    range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
    genScheme   = AST.ForGn nPar range
    -- Get the entity name and port names
    entity_id   = ent_id entity
    argports   = map (Monad.liftM fst) (ent_args entity)
    resport     = (Monad.liftM fst) (ent_res entity)
    -- Assign the ports
    inport      = mkAssocElemIndexed (argports!!0) (varToString arg) nPar
    outport     = mkAssocElemIndexed resport (varToString res) nPar
    clk_port    = mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
    portassigns = Maybe.catMaybes [inport,outport,clk_port]
    -- Generate the portmap
    mapLabel    = "map" ++ (AST.fromVHDLId entity_id)
    compins     = mkComponentInst mapLabel entity_id portassigns
    -- Return the generate functions
    genSm       = AST.CSGSm $ AST.GenerateSm label genScheme [] [compins]
    
genZipWithCall ::
  Entity
  -> [CoreSyn.CoreBndr]
  -> VHDLSession AST.ConcSm
genZipWithCall entity [arg1, arg2, res] = return $ genSm
  where
    -- Setup the generate scheme
    len         = (tfvec_len . Var.varType) res
    label       = mkVHDLExtId ("zipWithVector" ++ (varToString res))
    nPar        = AST.unsafeVHDLBasicId "n"
    range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
    genScheme   = AST.ForGn nPar range
    -- Get the entity name and port names
    entity_id   = ent_id entity
    argports    = map (Monad.liftM fst) (ent_args entity)
    resport     = (Monad.liftM fst) (ent_res entity)
    -- Assign the ports
    inport1     = mkAssocElemIndexed (argports!!0) (varToString arg1) nPar
    inport2     = mkAssocElemIndexed (argports!!1) (varToString arg2) nPar 
    outport     = mkAssocElemIndexed resport (varToString res) nPar
    clk_port    = mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
    portassigns = Maybe.catMaybes [inport1,inport2,outport,clk_port]
    -- Generate the portmap
    mapLabel    = "zipWith" ++ (AST.fromVHDLId entity_id)
    compins     = mkComponentInst mapLabel entity_id portassigns
    -- Return the generate functions
    genSm       = AST.CSGSm $ AST.GenerateSm label genScheme [] [compins]

genFoldlCall ::
  Entity
  -> [CoreSyn.CoreBndr]
  -> VHDLSession AST.ConcSm
genFoldlCall entity [startVal, inVec, resVal] = do
  let (vec, _) = splitAppTy (Var.varType inVec)
  let vecty = Type.mkAppTy vec (Var.varType startVal)
  vecType <- vhdl_ty vecty
  -- Setup the generate scheme
  let  len         = (tfvec_len . Var.varType) inVec
  let  genlabel       = mkVHDLExtId ("foldlVector" ++ (varToString inVec))
  let  blockLabel  = mkVHDLExtId ("foldlVector" ++ (varToString startVal))
  let  nPar        = AST.unsafeVHDLBasicId "n"
  let  range       = AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len-1))
  let  genScheme   = AST.ForGn nPar range
  -- Make the intermediate vector
  let  tmpVec      = AST.BDISD $ AST.SigDec (mkVHDLExtId "tmp") vecType Nothing
    -- Return the generate functions
  let genSm       = AST.GenerateSm genlabel genScheme []  [ AST.CSGSm (genFirstCell entity [startVal, inVec, resVal])
                                                          , AST.CSGSm (genOtherCell entity [startVal, inVec, resVal])
                                                          , AST.CSGSm (genLastCell entity [startVal, inVec, resVal])
                                                          ]
  return $ AST.CSBSm $ AST.BlockSm blockLabel [] (AST.PMapAspect []) [tmpVec] [AST.CSGSm genSm]
  where
    genFirstCell :: Entity -> [CoreSyn.CoreBndr] -> AST.GenerateSm 
    genFirstCell entity [startVal, inVec, resVal] = cellGn
      where
        cellLabel    = mkVHDLExtId "firstcell"
        cellGenScheme = AST.IfGn ((AST.PrimName $ AST.NSimple nPar)  AST.:=: (AST.PrimLit "0"))
        nPar        = AST.unsafeVHDLBasicId "n"
        -- Get the entity name and port names
        entity_id   = ent_id entity
        argports    = map (Monad.liftM fst) (ent_args entity)
        resport     = (Monad.liftM fst) (ent_res entity)
        -- Assign the ports
        inport1     = mkAssocElem (argports!!0) (varToString startVal)
        inport2     = mkAssocElemIndexed (argports!!1) (varToString inVec) nPar 
        outport     = mkAssocElemIndexed resport "tmp" nPar
        clk_port    = mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
        portassigns = Maybe.catMaybes [inport1,inport2,outport,clk_port]
        -- Generate the portmap
        mapLabel    = "cell" ++ (AST.fromVHDLId entity_id)
        compins     = mkComponentInst mapLabel entity_id portassigns
        -- Return the generate functions
        cellGn       = AST.GenerateSm cellLabel cellGenScheme [] [compins]
    genOtherCell :: Entity -> [CoreSyn.CoreBndr] -> AST.GenerateSm
    genOtherCell entity [startVal, inVec, resVal] = cellGn
      where
        len         = (tfvec_len . Var.varType) inVec
        cellLabel    = mkVHDLExtId "othercell"
        cellGenScheme = AST.IfGn $ AST.And ((AST.PrimName $ AST.NSimple nPar)  AST.:>: (AST.PrimLit "0"))
                                ((AST.PrimName $ AST.NSimple nPar)  AST.:<: (AST.PrimLit $ show (len-1)))
        nPar        = AST.unsafeVHDLBasicId "n"
        -- Get the entity name and port names
        entity_id   = ent_id entity
        argports    = map (Monad.liftM fst) (ent_args entity)
        resport     = (Monad.liftM fst) (ent_res entity)
        -- Assign the ports
        inport1     = mkAssocElemIndexed (argports!!0) "tmp" (AST.unsafeVHDLBasicId "n-1")
        inport2     = mkAssocElemIndexed (argports!!1) (varToString inVec) nPar 
        outport     = mkAssocElemIndexed resport "tmp" nPar
        clk_port    = mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
        portassigns = Maybe.catMaybes [inport1,inport2,outport,clk_port]
        -- Generate the portmap
        mapLabel    = "cell" ++ (AST.fromVHDLId entity_id)
        compins     = mkComponentInst mapLabel entity_id portassigns
        -- Return the generate functions
        cellGn      = AST.GenerateSm cellLabel cellGenScheme [] [compins]
    genLastCell :: Entity -> [CoreSyn.CoreBndr] -> AST.GenerateSm
    genLastCell entity [startVal, inVec, resVal] = cellGn
      where
        len         = (tfvec_len . Var.varType) inVec
        cellLabel    = mkVHDLExtId "lastCell"
        cellGenScheme = AST.IfGn ((AST.PrimName $ AST.NSimple nPar)  AST.:=: (AST.PrimLit $ show (len-1)))
        nPar        = AST.unsafeVHDLBasicId "n"
        -- Get the entity name and port names
        entity_id   = ent_id entity
        argports    = map (Monad.liftM fst) (ent_args entity)
        resport     = (Monad.liftM fst) (ent_res entity)
        -- Assign the ports
        inport1     = mkAssocElemIndexed (argports!!0) "tmp" (AST.unsafeVHDLBasicId "n-1")
        inport2     = mkAssocElemIndexed (argports!!1) (varToString inVec) nPar 
        outport     = mkAssocElemIndexed resport "tmp" nPar
        clk_port    = mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
        portassigns = Maybe.catMaybes [inport1,inport2,outport,clk_port]
        -- Generate the portmap
        mapLabel    = "cell" ++ (AST.fromVHDLId entity_id)
        compins     = mkComponentInst mapLabel entity_id portassigns
        -- Generate the output assignment
        assign      = mkUncondAssign (Left resVal) (AST.PrimName (AST.NIndexed (AST.IndexedName 
                              (AST.NSimple (mkVHDLExtId "tmp")) [AST.PrimLit $ show (len-1)])))
        -- Return the generate functions
        cellGn      = AST.GenerateSm cellLabel cellGenScheme [] [compins,assign]


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
