module Generate where

-- Standard modules
import qualified Control.Monad as Monad
import qualified Maybe

-- ForSyDe
import qualified ForSyDe.Backend.VHDL.AST as AST

-- GHC API
import CoreSyn
import qualified Var

-- Local imports
import Constants
import VHDLTypes
import VHDLTools
import CoreTools

-- | Generate a binary operator application. The first argument should be a
-- constructor from the AST.Expr type, e.g. AST.And.
genExprOp2 :: (AST.Expr -> AST.Expr -> AST.Expr) -> [AST.Expr] -> AST.Expr
genExprOp2 op [arg1, arg2] = op arg1 arg2

-- | Generate a unary operator application
genExprOp1 :: (AST.Expr -> AST.Expr) -> [AST.Expr] -> AST.Expr
genExprOp1 op [arg] = op arg

-- | Generate a function call from the Function Name and a list of expressions
--   (its arguments)
genExprFCall :: AST.VHDLId -> [AST.Expr] -> AST.Expr
genExprFCall fName args = 
   AST.PrimFCall $ AST.FCall (AST.NSimple fName)  $
             map (\exp -> Nothing AST.:=>: AST.ADExpr exp) args

-- | Generate a generate statement for the builtin function "map"
genMapCall :: 
  Entity -- | The entity to map
  -> [CoreSyn.CoreBndr] -- | The vectors
  -> AST.GenerateSm -- | The resulting generate statement
genMapCall entity [arg, res] = genSm
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
    genSm       = AST.GenerateSm label genScheme [] [compins]
    
genZipWithCall ::
  Entity
  -> [CoreSyn.CoreBndr]
  -> AST.GenerateSm
genZipWithCall entity [arg1, arg2, res] = genSm
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
    genSm       = AST.GenerateSm label genScheme [] [compins]

genUnconsVectorFuns :: AST.TypeMark -- ^ type of the vector elements
                    -> AST.TypeMark -- ^ type of the vector
                    -> [AST.SubProgBody]
genUnconsVectorFuns elemTM vectorTM  = 
  [ AST.SubProgBody exSpec      []                  [exExpr]                    
  , AST.SubProgBody replaceSpec [AST.SPVD replaceVar] [replaceExpr,replaceRet]   
  , AST.SubProgBody headSpec    []                  [headExpr]                  
  , AST.SubProgBody lastSpec    []                  [lastExpr]                  
  , AST.SubProgBody initSpec    [AST.SPVD initVar]  [initExpr, initRet]         
  , AST.SubProgBody tailSpec    [AST.SPVD tailVar]  [tailExpr, tailRet]         
  , AST.SubProgBody takeSpec    [AST.SPVD takeVar]  [takeExpr, takeRet]         
  , AST.SubProgBody dropSpec    [AST.SPVD dropVar]  [dropExpr, dropRet]    
  , AST.SubProgBody plusgtSpec  [AST.SPVD plusgtVar] [plusgtExpr, plusgtRet]
  , AST.SubProgBody emptySpec   [AST.SPCD emptyVar] [emptyExpr]
  , AST.SubProgBody singletonSpec [AST.SPVD singletonVar] [singletonRet] 
  , AST.SubProgBody copySpec    [AST.SPVD copyVar]      [copyExpr]
  ]
  where 
    ixPar   = AST.unsafeVHDLBasicId "ix"
    vecPar  = AST.unsafeVHDLBasicId "vec"
    nPar    = AST.unsafeVHDLBasicId "n"
    iId     = AST.unsafeVHDLBasicId "i"
    iPar    = iId
    aPar    = AST.unsafeVHDLBasicId "a"
    resId   = AST.unsafeVHDLBasicId "res"
    exSpec = AST.Function exId [AST.IfaceVarDec vecPar vectorTM,
                               AST.IfaceVarDec ixPar  naturalTM] elemTM
    exExpr = AST.ReturnSm (Just $ AST.PrimName $ AST.NIndexed 
              (AST.IndexedName (AST.NSimple vecPar) [AST.PrimName $ 
                AST.NSimple ixPar]))
    replaceSpec = AST.Function replaceId  [ AST.IfaceVarDec vecPar vectorTM
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
                              AST.AttribName (AST.NSimple vecPar) lengthId Nothing) AST.:-:
                                (AST.PrimLit "1"))   ]))
                Nothing
       --  res AST.:= vec(0 to i-1) & a & vec(i+1 to length'vec-1)
    replaceExpr = AST.NSimple resId AST.:=
           (vecSlice (AST.PrimLit "0") (AST.PrimName (AST.NSimple iPar) AST.:-: AST.PrimLit "1") AST.:&:
            AST.PrimName (AST.NSimple aPar) AST.:&: 
             vecSlice (AST.PrimName (AST.NSimple iPar) AST.:+: AST.PrimLit "1")
                      ((AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) lengthId Nothing)) 
                                                              AST.:-: AST.PrimLit "1"))
    replaceRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    vecSlice init last =  AST.PrimName (AST.NSlice 
                                        (AST.SliceName 
                                              (AST.NSimple vecPar) 
                                              (AST.ToRange init last)))
    headSpec = AST.Function headId [AST.IfaceVarDec vecPar vectorTM] elemTM
       -- return vec(0);
    headExpr = AST.ReturnSm (Just $ (AST.PrimName $ AST.NIndexed (AST.IndexedName 
                    (AST.NSimple vecPar) [AST.PrimLit "0"])))
    lastSpec = AST.Function lastId [AST.IfaceVarDec vecPar vectorTM] elemTM
       -- return vec(vec'length-1);
    lastExpr = AST.ReturnSm (Just $ (AST.PrimName $ AST.NIndexed (AST.IndexedName 
                    (AST.NSimple vecPar) 
                    [AST.PrimName (AST.NAttribute $ 
                                AST.AttribName (AST.NSimple vecPar) lengthId Nothing) 
                                                             AST.:-: AST.PrimLit "1"])))
    initSpec = AST.Function initId [AST.IfaceVarDec vecPar vectorTM] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-2);
    initVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) lengthId Nothing) AST.:-:
                                (AST.PrimLit "2"))   ]))
                Nothing
       -- resAST.:= vec(0 to vec'length-2)
    initExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimLit "0") 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) lengthId Nothing) 
                                                             AST.:-: AST.PrimLit "2"))
    initRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    tailSpec = AST.Function tailId [AST.IfaceVarDec vecPar vectorTM] vectorTM
       -- variable res : fsvec_x (0 to vec'length-2); 
    tailVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) lengthId Nothing) AST.:-:
                                (AST.PrimLit "2"))   ]))
                Nothing       
       -- res AST.:= vec(1 to vec'length-1)
    tailExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimLit "1") 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) lengthId Nothing) 
                                                             AST.:-: AST.PrimLit "1"))
    tailRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    takeSpec = AST.Function takeId [AST.IfaceVarDec nPar   naturalTM,
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
    dropSpec = AST.Function dropId [AST.IfaceVarDec nPar   naturalTM,
                                   AST.IfaceVarDec vecPar vectorTM ] vectorTM 
       -- variable res : fsvec_x (0 to vec'length-n-1);
    dropVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) lengthId Nothing) AST.:-:
                               (AST.PrimName $ AST.NSimple nPar)AST.:-: (AST.PrimLit "1")) ]))
               Nothing
       -- res AST.:= vec(n to vec'length-1)
    dropExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimName $ AST.NSimple nPar) 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) lengthId Nothing) 
                                                             AST.:-: AST.PrimLit "1"))
    dropRet =  AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    plusgtSpec = AST.Function plusgtId [AST.IfaceVarDec aPar   elemTM,
                                       AST.IfaceVarDec vecPar vectorTM] vectorTM 
    -- variable res : fsvec_x (0 to vec'length);
    plusgtVar = 
      AST.VarDec resId 
             (AST.SubtypeIn vectorTM
               (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                [AST.ToRange (AST.PrimLit "0")
                        (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) lengthId Nothing))]))
             Nothing
    plusgtExpr = AST.NSimple resId AST.:= 
                   ((AST.PrimName $ AST.NSimple aPar) AST.:&: 
                    (AST.PrimName $ AST.NSimple vecPar))
    plusgtRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    emptySpec = AST.Function emptyId [] vectorTM
    emptyVar = 
          AST.ConstDec resId 
              (AST.SubtypeIn vectorTM Nothing)
              (Just $ AST.PrimLit "\"\"")
    emptyExpr = AST.ReturnSm (Just $ AST.PrimName (AST.NSimple resId))
    singletonSpec = AST.Function singletonId [AST.IfaceVarDec aPar elemTM ] 
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
    copySpec = AST.Function copyId [AST.IfaceVarDec nPar   naturalTM,
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
