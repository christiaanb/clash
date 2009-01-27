module Main (main) where
import Language.Haskell.Syntax
import Language.Haskell.Pretty
import Language.Haskell.Parser
import GHC

main =
  do 
    let filename = "adder.hs"
    -- Read the file
    file <- readFile filename
    -- Parse the file
    let mode = ParseMode {parseFilename = filename}
        ParseOk mod = parseModuleWithMode mode file
    -- Print funky stuff
    --putStr $ foldl (\s d -> s ++ (show d) ++ "\n\n") "" (decls mod)
    putList (findfunc "exp_adder" (decls mod))

decls (HsModule _ _ _ _ decls) =
  decls

name (HsModule _ n _ _ _) =
  n

findfunc :: 
            String        -- Function name to find
         -> [HsDecl]      -- Decls to search
         -> [HsMatch]

findfunc name decls = foldl (findmatches name) [] decls

-- Look at a HsDecl and add all HsMatches in it with the sought name to res
findmatches name res (HsFunBind matches) = res ++ filter (filtermatch name) matches
findmatches name res _ = res

-- Look at a single match and see if it has the sought name
filtermatch name (HsMatch _ (HsIdent n) _ _ _) =
  n == name

-- Print a list of showable things, separated by newlines instead of ,
-- Also pretty prints them
putList :: (Show a, Pretty a) => [a] -> IO ()
putList (x:xs) =
  do
    indent 0 (show x)
    putStr "\n"
    putStr $ prettyPrint x
    putStr "\n\n"
    putList xs

putList [] =
  do return ()

-- Add indentations to the given string
indent :: Int -> String -> IO ()
indent n (x:xs) = do 
  if x `elem` "[(" 
    then do
      putChar x
      putStr "\n"
      putStr (replicate (n + 1) ' ')
      indent (n + 1) xs
    else if x `elem` "])" 
      then do
        putStr "\n"
        putStr (replicate (n - 1) ' ')
        putChar x
        indent (n - 1) xs
      else do 
        putChar x
        indent n xs

indent n [] = do return ()

-- vim: set ts=8 sw=2 sts=2 expandtab:
