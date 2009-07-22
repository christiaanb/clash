module CLasH.Utils.GhcTools where
-- Standard modules
import qualified System.IO.Unsafe

-- GHC API
import qualified GHC
import qualified DynFlags
import qualified TcRnMonad
import qualified MonadUtils
import qualified HscTypes
import qualified PrelNames

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
unsafeRunGhc :: FilePath -> GHC.Ghc a -> a
unsafeRunGhc libDir m =
  System.IO.Unsafe.unsafePerformIO $ do
      GHC.runGhc (Just libDir) $ do
        dflags <- GHC.getSessionDynFlags
        GHC.setSessionDynFlags dflags
        m

-- runTcM :: TcRnMonad.TcM a -> IO a
-- runTcM thing_inside = do
--   GHC.runGhc (Just GHC.Paths.libdir) $ do   
--     dflags <- GHC.getSessionDynFlags
--     GHC.setSessionDynFlags dflags
--     env <- GHC.getSession
--     HscTypes.ioMsgMaybe . MonadUtils.liftIO .  TcRnMonad.initTcPrintErrors env PrelNames.iNTERACTIVE $ do
--       thing_inside
