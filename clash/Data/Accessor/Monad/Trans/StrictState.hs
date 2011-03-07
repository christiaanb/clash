module Data.Accessor.Monad.Trans.StrictState where
  
import qualified Data.Accessor.Basic as Accessor
import qualified Control.Monad.Trans.State.Strict as State
import qualified Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.State.Strict (State, runState, StateT(runStateT), )

set :: Monad m => Accessor.T r a -> a -> StateT r m ()
set f x = State.modify (Accessor.set f x)

get :: Monad m => Accessor.T r a -> StateT r m a
get f = State.gets (Accessor.get f)

modify :: Monad m => Accessor.T r a -> (a -> a) -> StateT r m ()
modify f g = State.modify (Accessor.modify f g)

infix 1 %=, %:

(%=) :: Monad m => Accessor.T r a -> a -> StateT r m ()
(%=) = set

(%:) :: Monad m => Accessor.T r a -> (a -> a) -> StateT r m ()
(%:) = modify

lift :: Monad m => Accessor.T r s -> State s a -> StateT r m a
lift f m =
   do s0 <- get f
      let (a,s1) = runState m s0
      set f s1
      return a

liftT :: (Monad m) =>
   Accessor.T r s -> StateT s m a -> StateT r m a
liftT f m =
   do s0 <- get f
      (a,s1) <- Trans.lift $ runStateT m s0
      set f s1
      return a
