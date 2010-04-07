module CLasH.Utils where

-- Standard Imports
import qualified Maybe
import Data.Accessor
import qualified Data.Accessor.Monad.Trans.State as MonadState
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.State as State
  
-- Make a caching version of a stateful computatation.
makeCached :: (Monad m, Ord k) =>
  k -- ^ The key to use for the cache
  -> Accessor s (Map.Map k v) -- ^ The accessor to get at the cache
  -> State.StateT s m v -- ^ How to compute the value to cache?
  -> State.StateT s m v -- ^ The resulting value, from the cache or freshly
                        --   computed.
makeCached key accessor create = do
  cache <- MonadState.get accessor
  case Map.lookup key cache of
    -- Found in cache, just return
    Just value -> return value
    -- Not found, compute it and put it in the cache
    Nothing -> do
      value <- create
      MonadState.modify accessor (Map.insert key value)
      return value

unzipM :: (Monad m) =>
  m [(a, b)]
  -> m ([a], [b])
unzipM = Monad.liftM unzip

catMaybesM :: (Monad m) =>
  m [Maybe a]
  -> m [a]
catMaybesM = Monad.liftM Maybe.catMaybes

concatM :: (Monad m) =>
  m [[a]]
  -> m [a]
concatM = Monad.liftM concat

isJustM :: (Monad m) => m (Maybe a) -> m Bool
isJustM = Monad.liftM Maybe.isJust

andM, orM :: (Monad m) => m [Bool] -> m Bool
andM = Monad.liftM and
orM = Monad.liftM or

-- | Monadic versions of any and all. We reimplement them, since there
-- is no ready-made lifting function for them.
allM, anyM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM f = andM . (mapM f)
anyM f = orM . (mapM f)

mapAccumLM :: (Monad m) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ s []        =  return (s, [])
mapAccumLM f s (x:xs)    =  do
  (s',  y ) <- f s x
  (s'', ys) <- mapAccumLM f s' xs
  return (s'', y:ys)
