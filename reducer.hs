{-# LANGUAGE TypeOperators, TemplateHaskell, FlexibleContexts, TypeFamilies, 
             ScopedTypeVariables, RecordWildCards #-}
module Reducer where

import qualified Prelude as P
import CLasH.HardwareTypes
import CLasH.Translator.Annotations

-- =======================================
-- = System size configuration variables =
-- =======================================
type DataSize       = D64
type IndexSize      = D16
type DiscrSize      = D7
type AdderDepth     = D12

-- Derived configuration variables
type DiscrRange     = Pow2 DiscrSize
type AdderDepthPL   = AdderDepth :+: D3

-- =================
-- = Type Aliasses =
-- =================
type Shift          = Index D2
type DataInt        = Signed DataSize
type ArrayIndex     = Unsigned IndexSize
type Discr          = Index DiscrRange
type OutputSignal   = ((DataInt, ArrayIndex), Bool)

-- =================================
-- = Cell Definition and Accessors =
-- =================================
type CellType       = Bool                     
type Cell           = (CellType, (DataInt, Discr))

valid :: Cell -> Bool
valid (x, _) = x

value :: Cell -> DataInt
value (_, (v, _)) = v

discr :: Cell -> Discr
discr (_, (_, d)) = d

notValid :: Cell
notValid = (False, (0, 0))

-- ====================
-- = Helper functions =
-- ====================
v <<+ e = shiftIntoR v e
e +>> v = shiftIntoL v e

-- =======================
-- = Reducer State types =
-- =======================
data DiscrRecord =
  DiscrR { prev_index  ::  ArrayIndex
         , cur_discr   ::  Unsigned DiscrSize
         }
type DiscrState = State DiscrRecord
                            
type RippleState = 
  State (Vector (AdderDepthPL :+: D1) (CellType, Discr))

data BlockRecord = 
  Block { ptrs    ::  (Unsigned D4, Unsigned D4, Unsigned D4)
        , buf1    ::  MemState (AdderDepthPL :+: D1) DataInt
        , buf2    ::  MemState (AdderDepthPL :+: D1) DataInt
        }
type BlockState = State BlockRecord

type FpAdderState = 
  State ( ( (DataInt, DataInt, DataInt, DataInt)  -- Buffer input and double buffer output of the FPAdder
          , Vector AdderDepthPL (CellType, Discr) -- Validbits & discriminators of values in the FP pipeline
          )
        , FpPlaceholder
        )

type FpPlaceholder = 
  State (Vector AdderDepth DataInt)

data OutputRecord = 
  Outp { valid_mem :: RAM DiscrRange CellType
       , mem1      :: MemState DiscrRange DataInt
       , mem2      :: MemState DiscrRange DataInt
       , lutm      :: MemState DiscrRange ArrayIndex
       }                            
type OutputState = State OutputRecord

data ReducerRecord = 
  Reducer { discrState  :: DiscrState
          , rippleState :: RippleState
          , blockState  :: BlockState
          , pipeState   :: FpAdderState
          , resultState :: OutputState          
          , pipeline    :: ( Vector AdderDepth (Discr, ArrayIndex, Bool) -- Buffer link between discriminator and Result buffer                                                 
                           , CellType                                    -- Buffer Valid bit of the resultbuffer at T+1                                                 
                           , Vector D2 (DataInt, ArrayIndex)             -- Buffer Input (to encourage retiming)
                           , Vector D2 OutputSignal                      -- Buffer Output (to encourage retiming)
                           )
          }                              
type ReducerState   = State ReducerRecord

-- ===========================================================
-- = Discrimintor: Hands out new discriminator to the system =
-- ===========================================================
{-# ANN discriminator (InitState 'initDiscrState) #-}
discriminator :: 
  DiscrState -> 
  ArrayIndex -> 
  (DiscrState, Discr, Bool)
discriminator (State (DiscrR {..})) index = ( State DiscrR { prev_index = index
                                                           , cur_discr  = cur_discr'
                                                           }
                                            , discr
                                            , new_discr
                                            )
  where
    new_discr               = index /= prev_index
    cur_discr'  | new_discr = cur_discr + 1
                | otherwise = cur_discr
    discr                   = fromUnsigned cur_discr'

-- ======================================================
-- = Input Buffer: Buffers incomming inputs when needed =
-- ======================================================
{-# ANN rippleBuffer (InitState 'initRippleState) #-}
rippleBuffer :: 
  RippleState ->
  (Discr, Shift) ->
  (RippleState, (CellType, Discr), (CellType, Discr))
rippleBuffer (State buf) (inp, shift) = (State buf', out1, out2)
  where
    -- Write value
    next_valids              = (map (\(a, b) -> a) buf) <<+ True
    buf''                    = zipWith selects buf next_valids
    selects cell next_valid  = if (not (fst cell)) && next_valid then
                                 (True, inp)
                               else
                                 cell
    -- Shift values                            
    buf'        | shift == 2 = (False, 0) +>> ((False, 0) +>> buf'')
                | shift == 1 = (False, 0) +>> buf''
                | otherwise  = buf''
    -- Read values
    out1                     = last buf
    out2                     = last (init buf)
    
{-# ANN blockBuffer (InitState 'initBlockState) #-}
blockBuffer :: 
  BlockState ->
  (DataInt, Shift) ->
  (BlockState, DataInt, DataInt)
blockBuffer (State (Block {..})) (inp, shift) = ( State Block { ptrs = ptrs'
                                                              , buf1 = buf1'
                                                              , buf2 = buf2'
                                                              }
                                                , out1, out2)
  where 
    -- Do some state (un)packing
    (rd_ptr1, rd_ptr2, wr_ptr) = ptrs
    ptrs'                      = (rd_ptr1', rd_ptr2', wr_ptr')
    -- Update pointers               
    count                      = fromIndex shift
    (rd_ptr1', rd_ptr2')       = (rd_ptr1 + count, rd_ptr2 + count)
    wr_ptr'                    = wr_ptr + 1
    -- Write & Read from RAMs
    (buf1', out1)              = blockRAM buf1 inp (fromUnsigned rd_ptr1) (fromUnsigned wr_ptr) True
    (buf2', out2)              = blockRAM buf2 inp (fromUnsigned rd_ptr2) (fromUnsigned wr_ptr) True
    
-- ============================================
-- = Simulated pipelined floating point adder =
-- ============================================
{-# ANN fpAdder (InitState 'initPipeState) #-}
fpAdder :: 
  FpAdderState -> 
  (Cell, Cell) -> 
  (FpAdderState, (Cell, Cell))         
fpAdder (State ((buffer, pipe), adderState)) (arg1, arg2) = (State ((buffer', pipe'), adderState'), (pipeT_1, pipeT))
  where
    -- Do some state (un)packing
    (a1,a2,dataT_1,dataT)   = buffer
    buffer'                 = (value arg1, value arg2, adderOut, dataT_1)
    -- placeholder adder
    (adderState', adderOut) = fpPlaceholder adderState (a1, a2)
    -- Save corresponding indexes and valid bits      
    pipe'                   = (valid arg1, discr arg1) +>> pipe
    -- Produce output for time T and T+1
    pipeEndT                = last pipe
    pipeEndT_1              = last (init pipe)
    pipeT                   = (fst pipeEndT, (dataT, snd pipeEndT))
    pipeT_1                 = (fst pipeEndT_1,(dataT_1,snd pipeEndT_1))

{-# ANN fpPlaceholder (InitState 'initAdderState) #-}
fpPlaceholder :: FpPlaceholder -> (DataInt, DataInt) -> (FpPlaceholder, DataInt)
fpPlaceholder (State pipe) (arg1, arg2) = (State pipe', pipe_out)
  where
    pipe'       = (arg1 + arg2) +> init pipe
    pipe_out    = last pipe

-- ===================================================
-- = Optimized Partial Result Buffer, uses BlockRAMs =
-- ===================================================
{-# ANN resBuff (InitState 'initResultState) #-}                                   
resBuff :: 
  OutputState -> 
  ( Cell, Cell, Bool, (Discr, ArrayIndex, Bool)) -> 
  (OutputState, Cell, OutputSignal)
resBuff (State (Outp {..})) (pipeT, pipeT_1, new_cell, (discrN, index, new_discr)) = ( State Outp { valid_mem = valid_mem'
                                                                                                  , mem1      = mem1'
                                                                                                  , mem2      = mem2'
                                                                                                  , lutm      = lutm'
                                                                                                  }
                                                                                     , res_mem_out, output)
  where
    addrT                         = discr pipeT
    addrT_1                       = discr pipeT_1
    -- Purge completely reduced results from the system
    clean_mem   | new_discr       = replace valid_mem discrN False
                | otherwise       = valid_mem
    -- If a partial is fed  back to the pipeline, make its location invalid   
    valid_mem'  | new_cell        = replace clean_mem addrT True
                | otherwise       = replace clean_mem addrT False
    -- Two parrallel memories with the same write addr, but diff rdaddr for partial res and other for complete res
    (mem1', partial)              = blockRAM mem1 (value pipeT) addrT   addrT new_cell
    (mem2', complete)             = blockRAM mem2 (value pipeT) discrN  addrT new_cell
    -- Lut maps discriminators to array index
    (lutm', lut_out)              = blockRAM lutm index discrN discrN new_discr
    res_mem_out                   = (valid_mem!addrT_1, (partial,addrT))
    -- Output value to the system once a discriminator is reused
    output                        = ((complete,lut_out), new_discr && (valid_mem!discrN))

-- ================================================================
-- = Controller guides correct inputs to the floating point adder =
-- ================================================================
controller :: 
  (Cell, Cell, Cell, Cell) -> 
  (Cell, Cell, Shift, Bool)
controller (inp1, inp2, pipeT, from_res_mem) = (arg1, arg2, shift, to_res_mem)
  where
    (arg1, arg2, shift, to_res_mem)
      | valid pipeT && valid from_res_mem                          = (pipeT   , from_res_mem            , 0, False)
      | valid pipeT && valid inp1 && discr pipeT == discr inp1     = (pipeT   , inp1                    , 1, False)
      | valid inp1  && valid inp2 && discr inp1 == discr inp2      = (inp1    , inp2                    , 2, valid pipeT)
      | valid inp1                                                 = (inp1    , (True, (0, discr inp1)) , 1, valid pipeT)
      | otherwise                                                  = (notValid, notValid                , 0, valid pipeT)

-- =============================================
-- = Reducer: Wrap up all the above components =
-- =============================================
{-# ANN reducer TopEntity #-}
{-# ANN reducer (InitState 'initReducerState) #-}   
reducer :: 
  ReducerState -> 
  (DataInt, ArrayIndex) -> 
  (ReducerState, OutputSignal)
reducer (State (Reducer {..})) (data_in, index) = ( State Reducer { discrState  = discrState'
                                                                  , rippleState = rippleState'
                                                                  , blockState  = blockState'
                                                                  , pipeState   = pipeState'
                                                                  , resultState = resultState'
                                                                  , pipeline    = pipeline'
                                                                  }
                                                  , last outPipe)
  where
    -- Discriminator
    (discrState' , discrN, new_discr)       = discriminator discrState (snd (last inPipe))
    -- InputBuffer
    (rippleState' , (inp1V, inp1I), (inp2V, inp2I)) = rippleBuffer rippleState (discrN, shift)
    (blockState', inp1D, inp2D)             = blockBuffer blockState ((fst (last inPipe)), shift)
    (inp1,inp2)                             = ((inp1V,(inp1D,inp1I)),(inp2V,(inp2D,inp2I))) 
    -- FP Adder    
    (pipeState'  , (pipeT_1, pipeT))        = fpAdder pipeState (arg1, arg2)
    -- Result Buffer
    (resultState', from_res_mem, output')   = resBuff resultState (pipeT, pipeT_1, to_res_mem, last discrO)
    -- Controller
    (arg1,arg2,shift,to_res_mem)            = controller (inp1, inp2, pipeT, (valT, snd from_res_mem))
    -- Optimizations/Pipelining
    valT_1  | discr pipeT == discr pipeT_1  = not (valid from_res_mem)
            | otherwise                     = valid from_res_mem
    (discrO, valT, inPipe , outPipe)        = pipeline    
    pipeline'                               = ( (discrN, index, new_discr) +>> discrO
                                              , valT_1
                                              , (data_in, index) +>> inPipe
                                              , output' +>> outPipe
                                              )


-- ========================
-- = Initial State values =
-- ========================
initDiscrState :: DiscrRecord
initDiscrState = DiscrR { prev_index = 255
                        , cur_discr  = 127
                        }
                                         
initRippleState :: Vector (AdderDepthPL :+: D1) (CellType, Discr)
initRippleState = copy (False, 0)

initBlockState :: (Unsigned D4, Unsigned D4, Unsigned D4)
initBlockState = (0,1,0)
                     
initPipeState :: 
  ((DataInt,DataInt,DataInt,DataInt)
  , Vector AdderDepthPL (CellType, Discr)
  )
initPipeState = ((0,0,0,0),copy (False, 0))     

initAdderState :: Vector AdderDepth DataInt
initAdderState = copy 0

initResultState :: RAM DiscrRange CellType     
initResultState = copy False

initReducerState :: 
  ( Vector AdderDepth (Discr, ArrayIndex, Bool)
  , CellType
  , Vector D2 (DataInt, ArrayIndex)
  , Vector D2 OutputSignal
  )
initReducerState = (copy (0, 0, False), False, copy (0,0), copy ((0,0), False))

initstate :: ReducerState
initstate = State ( Reducer { discrState  = State initDiscrState
                            , rippleState = State initRippleState
                            , blockState  = State Block { ptrs = initBlockState
                                                        , buf1 = State (copy 0)
                                                        , buf2 = State (copy 0)
                                                        }
                            , pipeState   = State (initPipeState, State initAdderState)
                            , resultState = State Outp { valid_mem = initResultState 
                                                       , mem1      = State (copy 0)
                                                       , mem2      = State (copy 0)
                                                       , lutm      = State (copy 0)
                                                       }
                            , pipeline    = initReducerState
                            })

-- ==================
-- = Test Functions =
-- ==================          
run func state [] = []
run func state (i:input) = o:out
  where
    (state', o) = func state i
    out         = run func state' input

runReducer =  ( reduceroutput
              , validoutput
              , equal
              , allEqual
              )
  where
    -- input = randominput 900 7
    input  = siminput
    istate = initstate
    output = run reducer istate input
    reduceroutput = P.map fst (P.filter (\x -> (snd x)) output)
    validoutput   = [P.foldl (+) 0 
                      (P.map (\z -> P.toInteger (fst z)) 
                        (P.filter (\x -> (snd x) == i) input)) | i <- [0..30]]
    equal = [validoutput P.!! i == P.toInteger (fst (reduceroutput P.!! i)) | 
              i <- [0..30]]
    allEqual = P.foldl1 (&&) equal

siminput :: [(DataInt, ArrayIndex)]
siminput =  [(1,0),(5,1),(12,1),(4,2),(9,2),(2,2),(13,2),(2,2),(6,2),(1,2),(12,2),(13,3),(6,3),(11,3),(2,3),(11,3),(5,4),(11,4),(1,4),(7,4),(3,4),(4,4),(5,5),(8,5),(8,5),(13,5),(10,5),(7,5),(9,6),(9,6),(3,6),(11,6),(14,6),(13,6),(10,6),(4,7),(15,7),(13,7),(10,7),(10,7),(6,7),(15,7),(9,7),(1,7),(7,7),(15,7),(3,7),(13,7),(7,8),(3,9),(13,9),(2,10),(9,11),(10,11),(9,11),(2,11),(14,12),(14,12),(12,13),(7,13),(9,13),(7,14),(14,15),(5,16),(6,16),(14,16),(11,16),(5,16),(5,16),(7,17),(1,17),(13,17),(10,18),(15,18),(12,18),(14,19),(13,19),(2,19),(3,19),(14,19),(9,19),(11,19),(2,19),(2,20),(3,20),(13,20),(3,20),(1,20),(9,20),(10,20),(4,20),(8,21),(4,21),(8,21),(4,21),(13,21),(3,21),(7,21),(12,21),(7,21),(13,21),(3,21),(1,22),(13,23),(9,24),(14,24),(4,24),(13,25),(6,26),(12,26),(4,26),(15,26),(3,27),(6,27),(5,27),(6,27),(12,28),(2,28),(8,28),(5,29),(4,29),(1,29),(2,29),(9,29),(10,29),(4,30),(6,30),(14,30),(11,30),(15,31),(15,31),(2,31),(14,31),(9,32),(3,32),(4,32),(6,33),(15,33),(1,33),(15,33),(4,33),(3,33),(8,34),(12,34),(14,34),(15,34),(4,35),(4,35),(12,35),(14,35),(3,36),(14,37),(3,37),(1,38),(15,39),(13,39),(13,39),(1,39),(5,40),(10,40),(14,40),(1,41),(6,42),(8,42),(11,42),(11,43),(2,43),(11,43),(8,43),(12,43),(15,44),(14,44),(6,44),(8,44),(9,45),(5,45),(12,46),(6,46),(5,46),(4,46),(2,46),(9,47),(7,48),(1,48),(3,48),(10,48),(1,48),(6,48),(6,48),(11,48),(11,48),(8,48),(14,48),(5,48),(11,49),(1,49),(3,49),(11,49),(8,49),(3,50),(8,51),(9,52),(7,52),(7,53),(8,53),(10,53),(11,53),(14,54),(11,54),(4,54),(6,55),(11,55),(5,56),(7,56),(6,56),(2,56),(4,56),(12,56),(4,57),(12,57),(2,57),(14,57),(9,57),(12,57),(5,57),(11,57),(7,58),(14,58),(2,58),(10,58),(2,58),(14,58),(7,58),(12,58),(1,58),(11,59),(8,59),(2,59),(14,59),(6,59),(6,59),(6,59),(14,59),(4,59),(1,59),(4,60),(14,60),(6,60),(4,60),(8,60),(12,60),(1,60),(8,60),(8,60),(13,60),(10,61),(11,61),(6,61),(14,61),(10,61),(3,62),(10,62),(7,62),(14,62),(10,62),(4,62),(6,62),(1,62),(3,63),(3,63),(1,63),(1,63),(15,63),(7,64),(1,65),(4,65),(11,66),(3,66),(13,66),(2,67),(2,67),(5,68),(15,68),(11,68),(8,68),(4,69),(11,69),(12,69),(8,69),(7,70),(9,70),(6,70),(9,70),(11,70),(14,70),(5,71),(7,71),(11,72),(5,72),(3,72),(2,72),(1,73),(13,73),(9,73),(14,73),(5,73),(6,73),(14,73),(13,73),(3,74),(13,74),(3,75),(14,75),(10,75),(5,75),(3,75),(8,75),(9,76),(7,76),(10,76),(10,76),(8,77),(10,77),(11,77),(8,77),(2,77),(9,77),(9,77),(12,77),(4,77),(14,77),(10,77),(7,77),(3,77),(10,78),(8,79),(14,79),(11,80),(15,81),(6,81),(4,82),(6,82),(1,82),(12,83),(6,83),(11,83),(12,83),(15,83),(13,83),(1,84),(2,84),(11,84),(5,84),(2,84),(2,84),(3,84),(4,85),(6,86),(5,86),(15,86),(8,86),(9,86),(9,87),(9,87),(12,87),(4,87),(13,88),(14,88),(10,88),(11,88),(7,88),(4,88),(9,88),(1,88),(4,88),(4,88),(12,88),(8,89),(3,89),(10,89),(10,89),(5,89),(14,89),(11,89),(10,89),(5,90),(6,90),(10,90),(9,90),(8,90),(10,90),(5,90),(11,90),(6,90),(10,90),(7,90),(3,91),(7,91),(5,91),(15,91),(4,91),(6,91),(8,91),(1,91),(8,91),(12,92),(8,93),(9,93),(12,94),(8,94),(5,94),(11,95),(13,95),(5,96),(12,96),(8,96),(4,96),(7,97),(6,97),(4,97),(1,98),(5,98),(12,98),(13,99),(7,100),(12,100),(4,100),(10,100),(2,101),(3,101),(14,101),(12,101),(5,101),(2,101),(14,101),(15,101),(7,102),(13,102),(5,102),(7,102),(4,102),(8,102),(12,103),(15,103),(2,103),(2,103),(6,103),(6,103),(1,104),(14,104),(15,105),(3,105),(13,105),(1,105),(8,105),(8,105),(15,105),(13,105),(13,105),(6,105),(9,105),(6,106),(14,107),(12,107),(7,108),(7,108),(6,109),(11,109),(14,110),(8,111),(5,111),(15,111),(14,111),(3,111),(13,112),(12,112),(5,112),(10,112),(7,112),(5,113),(3,113),(2,113),(1,113),(15,113),(8,113),(10,113),(3,114),(6,114),(15,114),(4,115),(8,115),(1,115),(12,115),(5,115),(6,116),(2,116),(13,116),(12,116),(6,116),(10,117),(8,117),(14,118),(10,118),(3,118),(15,119),(6,119),(6,120),(5,121),(8,121),(4,122),(1,122),(9,123),(12,123),(6,124),(10,124),(2,124),(11,124),(9,125),(8,126),(10,126),(11,126),(14,126),(2,126),(5,126),(7,126),(3,127),(12,127),(15,128),(4,128),(1,129),(14,129),(8,129),(9,129),(6,129),(1,130),(11,130),(2,130),(13,130),(14,131),(2,131),(15,131),(4,131),(15,131),(8,131),(3,131),(8,132),(1,132),(13,132),(8,132),(5,132),(11,132),(14,132),(14,132),(4,132),(14,132),(5,132),(11,133),(1,133),(15,133),(8,133),(12,133),(8,134),(14,135),(11,136),(9,137),(3,137),(15,138),(1,138),(1,139),(4,139),(3,140),(10,140),(8,141),(12,141),(4,141),(12,141),(13,141),(10,141),(4,142),(6,142),(15,142),(4,142),(2,143),(14,143),(5,143),(10,143),(8,143),(9,143),(3,143),(11,143),(6,144),(3,145),(9,145),(10,145),(6,145),(11,145),(4,145),(13,145),(5,145),(4,145),(1,145),(3,145),(15,145),(14,146),(11,146),(9,146),(9,146),(10,146),(9,146),(3,146),(2,146),(10,146),(6,146),(7,146),(3,147),(4,147),(15,147),(11,147),(15,147),(1,147),(15,147),(14,147),(15,147),(5,147),(15,147),(4,147),(2,148),(12,149),(12,150),(10,150),(1,150),(7,151),(4,151),(14,151),(15,151),(5,152),(11,153),(3,153),(1,153),(1,153),(12,153),(1,154),(1,155),(11,155),(8,155),(3,155),(8,155),(8,155),(2,155),(9,156),(6,156),(12,156),(1,156),(3,156),(8,156),(5,157),(9,157),(12,157),(6,157),(8,158),(15,159),(2,159),(10,160),(10,160),(2,160),(6,160),(10,160),(8,160),(13,160),(12,161),(15,161),(14,161),(10,161),(13,161),(14,161),(3,161),(2,161),(1,161),(11,161),(7,161),(8,161),(4,162),(9,163),(3,164),(5,164),(9,164),(9,165),(7,165),(1,165),(6,166),(14,166),(3,166),(14,166),(4,166),(14,167),(5,167),(13,167),(12,167),(13,168),(9,168)]
