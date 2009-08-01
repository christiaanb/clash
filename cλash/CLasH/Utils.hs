module CLasH.Utils
  ( listBindings
  , listBind
  ) where

-- Standard Imports
import qualified Maybe

-- GHC API
import qualified CoreSyn
import qualified CoreUtils
import qualified HscTypes
import qualified Outputable
import qualified Var

-- Local Imports
import CLasH.Utils.GhcTools
import CLasH.Utils.Pretty
  
listBindings :: FilePath -> [FilePath] -> IO [()]
listBindings libdir filenames = do
  (cores,_,_,_,_) <- loadModules libdir filenames bogusFinder bogusFinder bogusFinder
  let binds = concat $ map (CoreSyn.flattenBinds . HscTypes.cm_binds) cores
  mapM (listBinding) binds
    where
      bogusFinder = (\x -> return $ Nothing)

listBinding :: (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -> IO ()
listBinding (b, e) = do
  putStr "\nBinder: "
  putStr $ show b
  putStr "\nType of Binder: \n"
  putStr $ Outputable.showSDoc $ Outputable.ppr $ Var.varType b
  putStr "\n\nExpression: \n"
  putStr $ prettyShow e
  putStr "\n\n"
  putStr $ Outputable.showSDoc $ Outputable.ppr e
  putStr "\n\nType of Expression: \n"
  putStr $ Outputable.showSDoc $ Outputable.ppr $ CoreUtils.exprType e
  putStr "\n\n"
  
-- | Show the core structure of the given binds in the given file.
listBind :: FilePath -> [FilePath] -> String -> IO ()
listBind libdir filenames name = do
  (_,corebind,_,coreexpr,_) <- loadModules libdir filenames bindFinder bindFinder exprFinder
  listBinding (Maybe.fromJust $ head corebind, Maybe.fromJust $ head coreexpr)
    where
      bindFinder  = findBind (hasVarName name)
      exprFinder  = findExpr (hasVarName name)