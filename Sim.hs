module Sim (simulate, Circuit, simulateIO) where
import Data.Typeable

simulate f input s = do
  putStr "Input: "
  putStr $ show input
  putStr "\nInitial State: "
  putStr $ show s
  putStr "\n\n"
  foldl1 (>>) (map (printOutput) output)
  where
    output = run f input s

-- A circuit with input of type a, state of type s and output of type b
type Circuit a s b = a -> s -> (s, b)

run :: Circuit a s b -> [a] -> s -> [(a, b, s)]
run f (i:input) s =
  (i, o, s'): (run f input s')
  where
    (s', o) = f i s
run _ [] _ = []

simulateIO :: (Read a, Show a, Show b, Show s) => Sim.Circuit a s b -> s -> IO()
simulateIO c s = do
  putStr "Initial State: "
  putStr $ show s
  putStr "\n\n"
  runIO c s

runIO :: (Read a, Show a, Show b, Show s) => Sim.Circuit a s b -> s -> IO()
runIO f s = do
  putStr "\nInput? "
  line <- getLine
  if (line == "") then
      return ()
    else
      let i = (read line) in do
      let (s', o) = f i s in do
      printOutput (i, o, s')
      simulateIO f s'

printOutput :: (Show i, Show o, Show s) => (i, o, s) -> IO ()
printOutput (i, o, s) = do
  putStr "Input: "
  putStr $ show i
  putStr "\nOutput: "
  putStr $ show o
  putStr "\nNew State: "
  putStr $ show s
  putStr "\n\n"
-- vim: set ts=8 sw=2 sts=2 expandtab:
