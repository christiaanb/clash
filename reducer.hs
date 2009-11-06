{-# LANGUAGE TypeOperators, TemplateHaskell, FlexibleContexts, TypeFamilies, ScopedTypeVariables, RecordWildCards #-}
module Main where

import System.Random
import System.IO.Unsafe (unsafePerformIO,unsafeInterleaveIO)
import qualified Prelude as P
import CLasH.HardwareTypes
import CLasH.Translator.Annotations

-- =======================================
-- = System size configuration variables =
-- =======================================

type DataSize       = D8
type IndexSize      = D8
type DiscrSize      = D7
type DiscrRange     = D127
type AdderDepth     = D14

-- =================
-- = Type Aliasses =
-- =================

type Shift          = RangedWord D2
type DataInt        = SizedWord DataSize
type ArrayIndex     = SizedWord IndexSize
type Discr          = RangedWord DiscrRange

type OutputSignal   = ( ( DataInt
                        , ArrayIndex
                        )
                      , Bool
                      )

data CellType       = Valid | NotValid
  deriving (Eq)
                      
type Cell           = ( CellType
                      , ( DataInt
                        , Discr
                        )
                      )

notValid :: Cell
notValid = (NotValid,(0::DataInt,0::Discr))    

-- ================================
-- = Cell type accessor functions =
-- ================================

valid :: Cell -> Bool
valid (Valid, _) = True
valid _          = False

value :: Cell -> DataInt
value (_, (v, _)) = v

discr :: Cell -> Discr
discr (_, (_, d)) = d

-- =======================
-- = Reducer State types =
-- =======================

data DiscrRecord    = DiscrR { prev_index  ::  ArrayIndex
                             , cur_discr   ::  SizedWord DiscrSize
                             }

type DiscrState     = State DiscrRecord

data CircRecord     = Circ  { mem   ::  Vector (AdderDepth :+: D1) (DataInt, Discr)
                            , rdptr ::  RangedWord AdderDepth
                            , wrptr ::  RangedWord AdderDepth
                            , count ::  RangedWord (AdderDepth :+: D1)
                            }

type CircState      = State CircRecord

type FpAdderState   = State (Vector AdderDepth Cell)

data OutputRecord   = Outp  { res_mem :: RAM DiscrRange Cell
                            , lut     :: MemState DiscrRange ArrayIndex
                            }

type OutputState    = State OutputRecord

data OutputRecordO  = OutpO { valid_mem :: RAM DiscrRange CellType
                            , mem1      :: MemState DiscrRange DataInt
                            , mem2      :: MemState DiscrRange DataInt
                            , lutm      :: MemState DiscrRange ArrayIndex
                            }
                            
type OutputStateO   = State OutputRecordO

data ReducerRecord  = Reducer { discrState  ::  DiscrState
                              , inputState  ::  CircState
                              , pipeState   ::  FpAdderState
                              , resultState ::  OutputStateO
                              }
                              
type ReducerState   = State ReducerRecord

data ReducerZeroRecord = ReducerZ { i0      :: ArrayIndex
                                  , inp     :: CircState
                                  , pipe    :: 
                                  ,
                                  }

-- ===========================================================
-- = Discrimintor: Hands out new discriminator to the system =
-- ===========================================================
discriminator ::  DiscrState -> (DataInt, ArrayIndex) -> (DiscrState, (DataInt, Discr), Bool)
discriminator (State (DiscrR {..})) (data_in, index) =  ( State ( DiscrR { prev_index = index
                                                                         , cur_discr  = cur_discr'
                                                                         })
                                                                , (data_in, discr)
                                                                , new_discr
                                                                )
  where
    new_discr                         = index /= prev_index
    cur_discr'  | new_discr           = cur_discr + 1
                | otherwise           = cur_discr
    discr                             = fromSizedWord cur_discr'

-- ======================================================
-- = Input Buffer: Buffers incomming inputs when needed =
-- ======================================================
circBuffer :: CircState ->
              ((DataInt, Discr), Shift) ->
              (CircState, Cell, Cell)
circBuffer (State (Circ {..})) (inp,shift) =  ( State ( Circ { mem   = mem' 
                                                             , rdptr = rdptr'
                                                             , wrptr = wrptr' 
                                                             , count = count'
                                                             })
                                                      , out1, out2
                                                      )
  where
    n               = fromIntegerT (undefined :: AdderDepth)
    (rdptr',count') | shift == 0  =                    (rdptr    , count + 1)
                    | shift == 1  = if rdptr == 0 then (n        , count    ) else
                                                       (rdptr - 1, count    )
                    | otherwise   = if rdptr == 1 then (n        , count - 1) else 
                                    if rdptr == 0 then (n - 1    , count - 1) else
                                                       (rdptr - 2, count - 1)
    rdptr2          | rdptr == 0  = n
                    | otherwise   = rdptr - 1 
    wrptr'          = if wrptr == 0 then n else wrptr - 1
    mem'            = replace mem wrptr inp
    out1            | count == 0  = notValid
                    | otherwise   = (Valid,mem!rdptr)
    out2            | count <= 1  = notValid
                    | otherwise   = (Valid,mem!rdptr2)
    
-- ============================================
-- = Simulated pipelined floating point adder =
-- ============================================
fpAdder ::  FpAdderState -> (Cell, Cell) -> (FpAdderState, Cell)         
fpAdder (State pipe) (arg1, arg2) = (State pipe', pipe_out)
  where
    new_head  | valid arg1  = (Valid, ((value arg1 + value arg2), discr arg1))
              | otherwise   = notValid
              
    pipe'     = new_head +> init pipe
    pipe_out  = last pipe

-- ==============================================================
-- = Partial Results buffers, purges completely reduced results =
-- ==============================================================
resBuff ::  OutputState -> ( Cell, Cell, ArrayIndex, (Discr, Bool)) -> (OutputState, Cell, OutputSignal)
resBuff (State (Outp {..})) (pipe_out, new_cell, index, (discrN, new_discr)) = ( State ( Outp { res_mem = res_mem''
                                                                                              , lut     = lut'
                                                                                              })
                                                                               , res_mem_out, output)
  where
    -- Purge completely reduced results from the system
    clean_mem     | new_discr       = replace res_mem discrN notValid
                  | otherwise       = res_mem
    -- If a partial is fed  back to the pipeline, make its location invalid      
    res_mem'	    | valid pipe_out	= replace clean_mem (discr pipe_out) notValid
		              | otherwise		    = clean_mem
    -- Write a new partial to memory if it is valid
    res_mem''	    | valid new_cell	= replace res_mem' (discr new_cell) new_cell
		              | otherwise		    = res_mem'
    -- Output a partial if it is needed, otherwise output invalid
    res_mem_out 	| valid pipe_out	= res_mem ! (discr pipe_out)
		              | otherwise		    = notValid
		-- Lut maps discriminators to array index
    (lut', lut_out)                 = blockRAM lut index discrN discrN new_discr
    -- Output value to the system once a discriminator is reused
    output'                         = res_mem ! discrN
    output                          = ( (value output', lut_out)
                                      , new_discr && valid output'
                                      )

-- ===================================================
-- = Optimized Partial Result Buffer, uses BlockRAMs =
-- ===================================================                                      
resBuffO ::  OutputStateO -> ( Cell, Cell, ArrayIndex, (Discr, Bool)) -> (OutputStateO, Cell, OutputSignal)
resBuffO (State (OutpO {..})) (pipe_out, new_cell, index, (discrN, new_discr)) = ( State ( OutpO { valid_mem = valid_mem'
                                                                                                 , mem1      = mem1'
                                                                                                 , mem2      = mem2'
                                                                                                 , lutm      = lutm'
                                                                                                 })
                                                                                 , res_mem_out, output)
  where
    addr                          = discr pipe_out
    -- Purge completely reduced results from the system
    clean_mem   | new_discr       = replace valid_mem discrN NotValid
                | otherwise       = valid_mem
    -- If a partial is fed  back to the pipeline, make its location invalid   
    valid_mem'  | valid new_cell  = replace clean_mem addr Valid
                | otherwise       = replace clean_mem addr NotValid
    -- Two parrallel memories with the same write addr, but diff rdaddr for partial res and other for complete res
    (mem1', partial)              = blockRAM mem1 (value new_cell) addr   addr (valid new_cell)
    (mem2', complete)             = blockRAM mem2 (value new_cell) discrN addr (valid new_cell)
    -- Lut maps discriminators to array index
    (lutm', lut_out)              = blockRAM lutm index discrN discrN new_discr
    res_mem_out                   = (valid_mem!addr, (partial,addr))
    -- Output value to the system once a discriminator is reused
    output                        = ((complete,lut_out), new_discr && (valid_mem!discrN) == Valid)

-- ================================================================
-- = Controller guides correct inputs to the floating point adder =
-- ================================================================
controller :: (Cell, Cell, Cell, Cell) -> (Cell, Cell, Shift, Cell)
controller (inp1, inp2, pipe_out, from_res_mem) = (arg1, arg2, shift, to_res_mem)
  where
    (arg1, arg2, shift, to_res_mem)
      | valid pipe_out && valid from_res_mem                          = (pipe_out, from_res_mem            , 0, notValid)
      | valid pipe_out && valid inp1 && discr pipe_out == discr inp1  = (pipe_out, inp1                    , 1, notValid)
      | valid inp1     && valid inp2 && discr inp1 == discr inp2      = (inp1    , inp2                    , 2, pipe_out)
      | valid inp1                                                    = (inp1    , (Valid, (0, discr inp1)), 1, pipe_out)
      | otherwise                                                     = (notValid, notValid                , 0, pipe_out)

-- =============================================
-- = Reducer: Wrap up all the above components =
-- =============================================
{-# ANN reducer TopEntity #-}
reducer ::  ReducerState -> (DataInt, ArrayIndex) -> (ReducerState, OutputSignal)
reducer (State (Reducer {..})) (data_in, index)   = (reducerState',output)
  where
    (discrState' , inpcell@(_,discrN), new_discr) = discriminator discrState (data_in,index)
    (inputState' , inp1   , inp2)                 = circBuffer inputState (inpcell, shift)
    (pipeState'  , pipe_out)                      = fpAdder pipeState (arg1, arg2)
    (resultState', from_res_mem, output)          = resBuffO resultState (pipe_out, to_res_mem, index, (discrN, new_discr))
    (arg1,arg2,shift,to_res_mem)                  = controller (inp1, inp2, pipe_out, from_res_mem)
    reducerState'                                 = State ( Reducer { discrState  = discrState'
                                                                    , inputState  = inputState'
                                                                    , pipeState   = pipeState'
                                                                    , resultState = resultState'
                                                                    })

-- -------------------------------------------------------
-- -- Test Functions
-- -------------------------------------------------------            
--             
-- "Default" Run function
run func state [] = []
run func state (i:input) = o:out
  where
    (state', o) = func state i
    out         = run func state' input

runReducerIO :: IO ()
runReducerIO = do
  let input = siminput
  let istate = initstate
  let output = run reducer istate input
  mapM_ (\x -> putStr $ ("(" P.++ (show x) P.++ ")\n")) output
  return ()

runReducer =  ( reduceroutput
              , validoutput
              , equal
              )
  where
    -- input = randominput 900 7
    input  = siminput
    istate = initstate
    output = run reducer istate input
    reduceroutput = P.map fst (filter (\x -> (snd x)) output)
    validoutput   = [P.foldl (+) 0 
                      (P.map (\z -> toInteger (fst z)) 
                        (filter (\x -> (snd x) == i) input)) | i <- [0..30]]
    equal = [validoutput!!i == toInteger (fst (reduceroutput!!i)) | 
              i <- [0..30]]
 
-- Generate infinite list of numbers between 1 and 'x'
randX :: Integer -> [Integer]   
randX x = randomRs (1,x) (unsafePerformIO newStdGen)

-- Generate random lists of indexes
randindex 15 i = randindex 1 i
randindex m i = (P.take n (repeat i)) P.++ (randindex (m+1) (i+1))
  where
    [n] = P.take 1 rnd
    rnd = randomRs (1,m) (unsafePerformIO newStdGen)

-- Combine indexes and values to generate random input for the reducer    
randominput n x = P.zip data_in index_in 
  where
    data_in   = P.map (fromInteger :: Integer -> DataInt) (P.take n (randX x))
    index_in  = P.map (fromInteger :: Integer -> ArrayIndex)
                        (P.take n (randindex 7 0))
main = runReducerIO

initstate :: ReducerState
initstate = State ( Reducer { discrState  = State ( DiscrR { prev_index = (255 :: ArrayIndex)
                                                           , cur_discr  = (127 :: SizedWord DiscrSize)
                                                           })
                            , inputState  = State ( Circ { mem   = copy (0::DataInt,0::Discr)
                                                         , rdptr = (14 :: RangedWord AdderDepth)
                                                         , wrptr = (14 :: RangedWord AdderDepth)
                                                         , count = (0 :: RangedWord (AdderDepth :+: D1))
                                                         })
                            , pipeState   = State ( copy notValid )
                            -- , resultState = State ( Outp { res_mem = copy notValid
                            --                              , lut     = State (copy (0::ArrayIndex))
                            --                              })
                            , resultState = State ( OutpO { valid_mem  = copy NotValid
                                                         , mem1       = State (copy (0::DataInt))
                                                         , mem2       = State (copy (0::DataInt))
                                                         , lutm       = State (copy (0::ArrayIndex))
                                                         })
                            })

{-# ANN siminput TestInput #-}
siminput :: [(DataInt, ArrayIndex)]
siminput =  [(1,0),(5,1),(12,1),(4,2),(9,2),(2,2),(13,2),(2,2),(6,2),(1,2),(12,2),(13,3),(6,3),(11,3),(2,3),(11,3),(5,4),(11,4),(1,4),(7,4),(3,4),(4,4),(5,5),(8,5),(8,5),(13,5),(10,5),(7,5),(9,6),(9,6),(3,6),(11,6),(14,6),(13,6),(10,6),(4,7),(15,7),(13,7),(10,7),(10,7),(6,7),(15,7),(9,7),(1,7),(7,7),(15,7),(3,7),(13,7),(7,8),(3,9),(13,9),(2,10),(9,11),(10,11),(9,11),(2,11),(14,12),(14,12),(12,13),(7,13),(9,13),(7,14),(14,15),(5,16),(6,16),(14,16),(11,16),(5,16),(5,16),(7,17),(1,17),(13,17),(10,18),(15,18),(12,18),(14,19),(13,19),(2,19),(3,19),(14,19),(9,19),(11,19),(2,19),(2,20),(3,20),(13,20),(3,20),(1,20),(9,20),(10,20),(4,20),(8,21),(4,21),(8,21),(4,21),(13,21),(3,21),(7,21),(12,21),(7,21),(13,21),(3,21),(1,22),(13,23),(9,24),(14,24),(4,24),(13,25),(6,26),(12,26),(4,26),(15,26),(3,27),(6,27),(5,27),(6,27),(12,28),(2,28),(8,28),(5,29),(4,29),(1,29),(2,29),(9,29),(10,29),(4,30),(6,30),(14,30),(11,30),(15,31),(15,31),(2,31),(14,31),(9,32),(3,32),(4,32),(6,33),(15,33),(1,33),(15,33),(4,33),(3,33),(8,34),(12,34),(14,34),(15,34),(4,35),(4,35),(12,35),(14,35),(3,36),(14,37),(3,37),(1,38),(15,39),(13,39),(13,39),(1,39),(5,40),(10,40),(14,40),(1,41),(6,42),(8,42),(11,42),(11,43),(2,43),(11,43),(8,43),(12,43),(15,44),(14,44),(6,44),(8,44),(9,45),(5,45),(12,46),(6,46),(5,46),(4,46),(2,46),(9,47),(7,48),(1,48),(3,48),(10,48),(1,48),(6,48),(6,48),(11,48),(11,48),(8,48),(14,48),(5,48),(11,49),(1,49),(3,49),(11,49),(8,49),(3,50),(8,51),(9,52),(7,52),(7,53),(8,53),(10,53),(11,53),(14,54),(11,54),(4,54),(6,55),(11,55),(5,56),(7,56),(6,56),(2,56),(4,56),(12,56),(4,57),(12,57),(2,57),(14,57),(9,57),(12,57),(5,57),(11,57),(7,58),(14,58),(2,58),(10,58),(2,58),(14,58),(7,58),(12,58),(1,58),(11,59),(8,59),(2,59),(14,59),(6,59),(6,59),(6,59),(14,59),(4,59),(1,59),(4,60),(14,60),(6,60),(4,60),(8,60),(12,60),(1,60),(8,60),(8,60),(13,60),(10,61),(11,61),(6,61),(14,61),(10,61),(3,62),(10,62),(7,62),(14,62),(10,62),(4,62),(6,62),(1,62),(3,63),(3,63),(1,63),(1,63),(15,63),(7,64),(1,65),(4,65),(11,66),(3,66),(13,66),(2,67),(2,67),(5,68),(15,68),(11,68),(8,68),(4,69),(11,69),(12,69),(8,69),(7,70),(9,70),(6,70),(9,70),(11,70),(14,70),(5,71),(7,71),(11,72),(5,72),(3,72),(2,72),(1,73),(13,73),(9,73),(14,73),(5,73),(6,73),(14,73),(13,73),(3,74),(13,74),(3,75),(14,75),(10,75),(5,75),(3,75),(8,75),(9,76),(7,76),(10,76),(10,76),(8,77),(10,77),(11,77),(8,77),(2,77),(9,77),(9,77),(12,77),(4,77),(14,77),(10,77),(7,77),(3,77),(10,78),(8,79),(14,79),(11,80),(15,81),(6,81),(4,82),(6,82),(1,82),(12,83),(6,83),(11,83),(12,83),(15,83),(13,83),(1,84),(2,84),(11,84),(5,84),(2,84),(2,84),(3,84),(4,85),(6,86),(5,86),(15,86),(8,86),(9,86),(9,87),(9,87),(12,87),(4,87),(13,88),(14,88),(10,88),(11,88),(7,88),(4,88),(9,88),(1,88),(4,88),(4,88),(12,88),(8,89),(3,89),(10,89),(10,89),(5,89),(14,89),(11,89),(10,89),(5,90),(6,90),(10,90),(9,90),(8,90),(10,90),(5,90),(11,90),(6,90),(10,90),(7,90),(3,91),(7,91),(5,91),(15,91),(4,91),(6,91),(8,91),(1,91),(8,91),(12,92),(8,93),(9,93),(12,94),(8,94),(5,94),(11,95),(13,95),(5,96),(12,96),(8,96),(4,96),(7,97),(6,97),(4,97),(1,98),(5,98),(12,98),(13,99),(7,100),(12,100),(4,100),(10,100),(2,101),(3,101),(14,101),(12,101),(5,101),(2,101),(14,101),(15,101),(7,102),(13,102),(5,102),(7,102),(4,102),(8,102),(12,103),(15,103),(2,103),(2,103),(6,103),(6,103),(1,104),(14,104),(15,105),(3,105),(13,105),(1,105),(8,105),(8,105),(15,105),(13,105),(13,105),(6,105),(9,105),(6,106),(14,107),(12,107),(7,108),(7,108),(6,109),(11,109),(14,110),(8,111),(5,111),(15,111),(14,111),(3,111),(13,112),(12,112),(5,112),(10,112),(7,112),(5,113),(3,113),(2,113),(1,113),(15,113),(8,113),(10,113),(3,114),(6,114),(15,114),(4,115),(8,115),(1,115),(12,115),(5,115),(6,116),(2,116),(13,116),(12,116),(6,116),(10,117),(8,117),(14,118),(10,118),(3,118),(15,119),(6,119),(6,120),(5,121),(8,121),(4,122),(1,122),(9,123),(12,123),(6,124),(10,124),(2,124),(11,124),(9,125),(8,126),(10,126),(11,126),(14,126),(2,126),(5,126),(7,126),(3,127),(12,127),(15,128),(4,128),(1,129),(14,129),(8,129),(9,129),(6,129),(1,130),(11,130),(2,130),(13,130),(14,131),(2,131),(15,131),(4,131),(15,131),(8,131),(3,131),(8,132),(1,132),(13,132),(8,132),(5,132),(11,132),(14,132),(14,132),(4,132),(14,132),(5,132),(11,133),(1,133),(15,133),(8,133),(12,133),(8,134),(14,135),(11,136),(9,137),(3,137),(15,138),(1,138),(1,139),(4,139),(3,140),(10,140),(8,141),(12,141),(4,141),(12,141),(13,141),(10,141),(4,142),(6,142),(15,142),(4,142),(2,143),(14,143),(5,143),(10,143),(8,143),(9,143),(3,143),(11,143),(6,144),(3,145),(9,145),(10,145),(6,145),(11,145),(4,145),(13,145),(5,145),(4,145),(1,145),(3,145),(15,145),(14,146),(11,146),(9,146),(9,146),(10,146),(9,146),(3,146),(2,146),(10,146),(6,146),(7,146),(3,147),(4,147),(15,147),(11,147),(15,147),(1,147),(15,147),(14,147),(15,147),(5,147),(15,147),(4,147),(2,148),(12,149),(12,150),(10,150),(1,150),(7,151),(4,151),(14,151),(15,151),(5,152),(11,153),(3,153),(1,153),(1,153),(12,153),(1,154),(1,155),(11,155),(8,155),(3,155),(8,155),(8,155),(2,155),(9,156),(6,156),(12,156),(1,156),(3,156),(8,156),(5,157),(9,157),(12,157),(6,157),(8,158),(15,159),(2,159),(10,160),(10,160),(2,160),(6,160),(10,160),(8,160),(13,160),(12,161),(15,161),(14,161),(10,161),(13,161),(14,161),(3,161),(2,161),(1,161),(11,161),(7,161),(8,161),(4,162),(9,163),(3,164),(5,164),(9,164),(9,165),(7,165),(1,165),(6,166),(14,166),(3,166),(14,166),(4,166),(14,167),(5,167),(13,167),(12,167),(13,168),(9,168)]

