module CLasH.Utils where
  
import qualified GHC.Paths
import qualified "clash" CLasH.Utils as Original (listBindings, listBind)

-- | Show the core structure of all the binds in the given file.
listBindings :: [FilePath] -> IO [()]
listBindings filenames = do
  let libdir = GHC.Paths.libdir
  Original.listBindings libdir filename

-- | Show the core structure of the given binds in the given file.  
listBind :: [FilePath] -> String -> IO ()
listBind filename name = do
  let libdir = GHC.Paths.libdir
  Original.listBind libdir filename name