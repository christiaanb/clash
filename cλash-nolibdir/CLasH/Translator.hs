module CLasH.Translator where

import qualified GHC.Paths
import qualified "clash" CLasH.Translator as Original (makeVHDL, makeVHDLAnn, listBindings, listBind)

makeVHDL :: String -> String -> Bool -> IO ()
makeVHDL filename name stateful = do
  let libdir = GHC.Paths.libdir
  Original.makeVHDL libdir filename name stateful
  
makeVHDLAnn :: String -> IO ()
makeVHDLAnn filename = do
  let libdir = GHC.Paths.libdir
  Original.makeVHDLAnn libdir filename

listBindings :: String -> IO [()]
listBindings filename = do
  let libdir = GHC.Paths.libdir
  Original.listBindings libdir filename
  
listBind :: String -> String -> IO ()
listBind filename name = do
  let libdir = GHC.Paths.libdir
  Original.listBind libdir filename name
