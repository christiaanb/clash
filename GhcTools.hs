module GhcTools where
-- Standard modules
import qualified System.IO.Unsafe

-- GHC API
import qualified GHC
import qualified GHC.Paths
import qualified DynFlags

-- Change a DynFlag from within the Ghc monad. Strangely enough there seems to
-- be no standard function to do exactly this.
setDynFlag :: DynFlags.DynFlag -> GHC.Ghc ()
setDynFlag dflag = do
  dflags <- GHC.getSessionDynFlags
  let dflags' = DynFlags.dopt_set dflags dflag
  GHC.setSessionDynFlags dflags'
  return ()

-- We don't want the IO monad sprinkled around everywhere, so we hide it.
-- This should be safe as long as we only do simple things in the GhcMonad
-- such as interface lookups and evaluating simple expressions that
-- don't have side effects themselves (Or rather, that don't use
-- unsafePerformIO themselves, since normal side effectful function would
-- just return an IO monad when they are evaluated).
unsafeRunGhc :: GHC.Ghc a -> a
unsafeRunGhc m =
  System.IO.Unsafe.unsafePerformIO $ 
      GHC.runGhc (Just GHC.Paths.libdir) $ do
        dflags <- GHC.getSessionDynFlags
        GHC.setSessionDynFlags dflags
        m
