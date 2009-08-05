module CLasH.Utils
  ( listBindings
  , listBind
  , makeCached
  ) where

-- Standard Imports
import qualified Maybe
import Data.Accessor
import qualified Data.Map as Map
import qualified Control.Monad.Trans.State as State

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

-- Make a caching version of a stateful computatation.
makeCached :: (Monad m, Ord k) =>
  k -- ^ The key to use for the cache
  -> Accessor s (Map.Map k v) -- ^ The accessor to get at the cache
  -> State.StateT s m v -- ^ How to compute the value to cache?
  -> State.StateT s m v -- ^ The resulting value, from the cache or freshly
                        --   computed.
makeCached key accessor create = do
  cache <- getA accessor
  case Map.lookup key cache of
    -- Found in cache, just return
    Just value -> return value
    -- Not found, compute it and put it in the cache
    Nothing -> do
      value <- create
      modA accessor (Map.insert key value)
      return value
