{-# LANGUAGE TypeOperators, TemplateHaskell, FlexibleContexts, TypeFamilies #-}
module Reducer where

import System.Random
import System.IO.Unsafe (unsafePerformIO,unsafeInterleaveIO)

import qualified Prelude as P
import CLasH.HardwareTypes
import CLasH.Translator.Annotations

type DataSize       = D8
type IndexSize      = D8
type DiscrSize      = D3
type DiscrRange     = D7
type AdderDepth     = D2

type DataInt        = SizedWord DataSize
type ArrayIndex     = SizedWord IndexSize
type Discr          = RangedWord DiscrRange

type ReducerState   = State ( DiscrState
                      , InputState
                      , FpAdderState
                      , OutputState
                      )
type ReducerSignal  = ( ( DataInt
                        , Discr
                        )
                      , Bit
                      )
                      
type OutputSignal   = ( (DataInt
                        , ArrayIndex
                        )
                      , Bit
                      )

type DiscrState     = State ( ArrayIndex
                      , SizedWord DiscrSize
                      )
                     
type InputState     = State ( Vector (AdderDepth :+: D1) ReducerSignal
                      , RangedWord AdderDepth
                      )

type FpAdderState   = State (Vector AdderDepth ReducerSignal)

type OutputState    = State ( MemState DiscrRange DataInt
                            , MemState DiscrRange DataInt
                            , MemState DiscrRange ArrayIndex
                            , RAM DiscrRange Bit
                      )
{-
Discriminator adds a discriminator to each input value

State:
prev_index: previous index
cur_discr: current discriminator

Input:
data_in: input value
index: row index

Output:
data_in: output value
discr: discriminator belonging to output value
new_discr: value of new discriminator, is -1 if cur_discr hasn't changed
index: Index belonging to the new discriminator 
-}
discriminator ::  DiscrState -> (DataInt, ArrayIndex) -> 
                  ( DiscrState
                  , ((DataInt, Discr), (Bit, ArrayIndex))
                  )
discriminator (State (prev_index,cur_discr)) (data_in, index) = 
  (State (prev_index', cur_discr'), ((data_in, discr),(new_discr, index)))
  where
    -- Update discriminator if index changes
    cur_discr'  | prev_index == index = cur_discr
                | otherwise           = cur_discr + 1
    -- Notify OutputBuffer if a new discriminator becomes in use
    new_discr   | prev_index == index = Low
                | otherwise           = High
    prev_index'                       = index
    discr                             = fromSizedWord cur_discr'

{-
Second attempt at Fifo
Uses "write pointer"... ugly...
Can potentially be mapped to hardware

State:
mem: content of the FIFO
wrptr: points to first free spot in the FIFO

Input:
inp: (value,discriminator) pair
enable: Flushes 2 values from FIFO if 2, 1 value from FIFO if 1, no values 
        from FIFO if 0
  
Output
out1: ((value, discriminator),valid) pair of head FIFO
out2: ((value, discriminator),valid) pair of second register FIFO

valid indicates if the output contains a valid discriminator
-}
inputBuffer ::  InputState -> 
                ((DataInt, Discr), RangedWord D2) -> 
                (InputState, ReducerSignal, ReducerSignal)
inputBuffer (State (mem,wrptr)) (inp,enable) = (State (mem',wrptr'),out1, out2)
  where
    out1                  = last mem -- output head of FIFO
    out2                  = last (init mem) -- output 2nd element
    -- Update free spot pointer according to value of 'enable' 
    wrptr'  | enable == 0 = wrptr - 1
            | enable == 1 = wrptr
            | otherwise   = wrptr + 1
    -- Write value to free spot
    mem''                 = replace mem wrptr (inp,High)
    -- Flush values at head of fifo according to value of 'enable'
    mem'    | enable == 0 = mem'' 
            | enable == 1 = zero +> (init mem'')
            | otherwise   = zero +> (zero +> (init(init mem'')))
    zero                  = (((0::DataInt),(0::Discr)),(Low::Bit))
            
            
{-
floating point Adder 

output discriminator becomes discriminator of the first operant

State:
state: "pipeline" of the fp Adder

Input:
input1: out1 of the FIFO
input2: out2 of the FIFO
grant: grant signal comming from the controller, determines which value enters 
       the pipeline
mem_out: Value of the output buffer for the read address
         Read address for the output buffer is the discriminator at the top of 
        the adder pipeline

Output:
output: ((Value, discriminator),valid) pair at the top of the adder pipeline

valid indicates if the output contains a valid discriminator
-}
fpAdder ::  FpAdderState -> 
            ( ReducerSignal
            , ReducerSignal
            , (RangedWord D2, RangedWord D2)
            , ReducerSignal
            ) ->        
            (FpAdderState, ReducerSignal)         
fpAdder (State state) (input1, input2, grant, mem_out) = (State state', output)
  where
    -- output is head of the pipeline
    output    = last state
    -- First value of 'grant' determines operant 1
    operant1  | (fst grant) == 0  = fst (fst (last state))
              | (fst grant) == 1  = fst (fst input2)
              | otherwise         = 0
    -- Second value of 'grant' determine operant 2
    operant2  | (snd grant) == 0  = fst (fst input1)
              | (snd grant) == 1  = fst (fst mem_out)
              | (otherwise)       = 0
    -- Determine discriminator for new value
    discr     | (snd grant) == 0  = snd (fst input1)
              | (snd grant) == 1  = snd (fst (last state))
              | otherwise         = 0
    -- Determine if discriminator should be marked as valid
    valid     | grant == (2,2)    = Low
              | otherwise         = High
    -- Shift addition of the two operants into the pipeline
    state'    = (((operant1 + operant2),discr),valid) +> (init state)

{-
Output logic - Determines when values are released from blockram to the output

State:
mem: memory belonging to the blockRAM
lut: Lookup table that maps discriminators to Index'
valid: Lookup table for 'validity' of the content of the blockRAM

Input:
discr: Value of the newest discriminator when it first enters the system. 
       (-1) otherwise.
index: Index belonging to the newest discriminator
data_in: value to be written to RAM
rdaddr: read address
wraddr: write address
wrenable: write enabled flag

Output:
data_out: value of RAM at location 'rdaddr'
output: Reduced row when ready, (-1) otherwise
-}
outputter ::  OutputState -> 
              ( Discr
              , ArrayIndex
              , Bit
              , DataInt
              , Discr
              , Discr
              , Bit
              ) -> 
              (OutputState, ReducerSignal, OutputSignal)
outputter (State (mem1, mem2, lut, valid))
  (discr, index, new_discr, data_in, rdaddr, wraddr, wrenable) = 
  ((State (mem1', mem2', lut', valid')), data_out, output)
  where
    -- Lut is updated when new discriminator/index combination enters system        
    (lut', lut_out)             = blockRAM lut index discr discr new_discr
    -- Location becomes invalid when Reduced row leaves system        
    valid'' | (new_discr /= Low) && ((valid!discr) /= Low) = 
                                  replace valid discr Low
            | otherwise         = valid
    -- Location becomes invalid when it is fed back into the pipeline
    valid'  | wrenable == Low   = replace valid'' rdaddr Low
            | otherwise         = replace valid'' wraddr High
    (mem1', mem_out1)           = blockRAM mem1 data_in rdaddr wraddr wrenable
    (mem2', mem_out2)           = blockRAM mem2 data_in discr wraddr wrenable
    data_out                    = ( ( (mem_out1)
                                    , rdaddr
                                    )
                                  , (valid!rdaddr)
                                  )
    -- Reduced row is released when new discriminator enters system
    -- And the position at the discriminator holds a valid value
    output                      = ( ( (mem_out2)
                                    , (lut_out)
                                    )
                                  , (new_discr `hwand` (valid!discr))
                                  )

{-
Arbiter determines which rules are valid

Input:
fp_out: output of the adder pipeline
mem_out: data_out of the output logic
inp1: Head of the input FIFO
inp2: Second element of input FIFO

Output:
r4 - r0: vector of rules, rule is invalid if it's 0, valid otherwise
-}
arbiter :: (ReducerSignal, ReducerSignal, ReducerSignal, ReducerSignal) ->  
            Vector D5 Bit
arbiter (fp_out, mem_out, inp1, inp2) = (r4 +> (r3 +> (r2 +> (r1 +> (singleton r0)))))
  where -- unpack parameters
    fp_valid    = snd fp_out
    next_valid  = snd mem_out
    inp1_valid  = snd inp1
    inp2_valid  = snd inp2
    fp_discr    = snd (fst fp_out)
    next_discr  = snd (fst mem_out)
    inp1_discr  = snd (fst inp1)
    inp2_discr  = snd (fst inp2)
    -- Apply rules
    r0  | (fp_valid /= Low) && (next_valid /= Low) && (fp_discr == next_discr)  
                                      = High
        | otherwise                   = Low
    r1  | (fp_valid /= Low) && (inp1_valid /= Low) && (fp_discr == inp1_discr)  
                                      = High
        | otherwise                   = Low
    r2  | (inp1_valid /= Low) && (inp2_valid /= Low) && 
          (inp1_discr == inp2_discr)  = High
        | otherwise                   = Low
    r3  | inp1_valid /= Low           = High
        | otherwise                   = Low
    r4                                = High

{-
Controller determines which values are fed into the pipeline
and if the write enable flag for the Output RAM should be set
to true. Also determines how many values should be flushed from
the input FIFO.

Input:
fp_out: output of the adder pipeline
mem_out: data_out of the output logic
inp1: Head of input FIFO
inp2: Second element of input FIFO

Output:
grant: Signal that determines operants for the adder
enable: Number of values to be flushed from input buffer
wr_enable: Determine if value of the adder should be written to RAM
-}
controller :: (ReducerSignal, ReducerSignal, ReducerSignal, ReducerSignal) -> 
                ((RangedWord D2, RangedWord D2), RangedWord D2, Bit)
controller (fp_out,mem_out,inp1,inp2) = (grant,enable,wr_enable)
  where
    -- Arbiter determines which rules are valid
    valid       = arbiter (fp_out,mem_out,inp1,inp2)
    -- Determine which values should be fed to the adder
    grant       = if (valid!(4 :: RangedWord D4) == High) 
                  then (0,1) 
                  else if ((drop d3 valid) == $(vectorTH [High,Low])) 
                  then (0,0) 
                  else if ((drop d2 valid) == $(vectorTH [High,Low,Low])) 
                  then (1,0) 
                  else if ((drop d1 valid) == $(vectorTH [High,Low,Low,Low])) 
                  then (2,0) 
                  else (2,2)
    -- Determine if some values should be flushed from input FIFO
    enable      = if (grant == (1,0)) 
                  then 2 
                  else if ((grant == (0,0)) || (grant == (2,0))) 
                  then 1 
                  else 0
    -- Determine if the output value of the adder should be written to RAM
    wr_enable'  = if (valid!(4 :: RangedWord D4) == High) 
                  then Low 
                  else if ((drop d3 valid) == $(vectorTH [High,Low])) 
                  then Low 
                  else if ((drop d2 valid) == $(vectorTH [High,Low,Low]))
                  then High
                  else if ((drop d1 valid) == $(vectorTH [High,Low,Low,Low])) 
                  then High 
                  else High
    wr_enable   = if ((snd fp_out) /= Low) then wr_enable' else Low

{-
Reducer

Combines all the earlier defined functions. Uses the second implementation
of the input FIFO.

Parameter: 
'n': specifies the max discriminator value.

State: all the states of the used functions

Input: (value,index) combination

Output: reduced row
-}
{-# ANN reducer TopEntity #-}
reducer ::  ReducerState -> 
            (DataInt, ArrayIndex) -> 
            (ReducerState, OutputSignal)
reducer (State (discrstate,inputstate,fpadderstate,outputstate)) input = 
  (State (discrstate',inputstate',fpadderstate',outputstate'),output)
  where
    (discrstate', discr_out)              = discriminator discrstate input
    (inputstate',fifo_out1, fifo_out2)    = inputBuffer inputstate (
                                            (fst discr_out), enable)
    (fpadderstate', fp_out)               = fpAdder fpadderstate (fifo_out1, 
                                                fifo_out2, grant, mem_out)
    discr                                 = snd (fst discr_out)
    new_discr                             = fst (snd discr_out)
    index                                 = snd (snd discr_out)
    rdaddr                                = snd (fst fp_out)
    wraddr                                = rdaddr
    data_in                               = fst (fst fp_out)
    (outputstate', mem_out, output)       = outputter outputstate (discr,
                                            index, new_discr, data_in, rdaddr, 
                                            wraddr, wr_enable)
    (grant,enable,wr_enable)              = controller (fp_out, mem_out, 
                                            fifo_out1, fifo_out2)


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
-- 
-- -- "Special" Run function, also outputs new state      
-- run' func state [] = ([],[])   
-- run' func state (i:input) = ((o:out), (state':ss))
--   where
--     (state',o)  = func state i
--     (out,ss)         = run' func state' input
-- 
-- Run reducer
runReducer =  ( reduceroutput
              , validoutput
              , equal
              )
  where
    input = siminput
    istate = initstate
    output = run reducer istate input
    reduceroutput = P.map fst (filter (\x -> (snd x) /= Low) output)
    validoutput   = [P.foldl (+) 0 
                      (P.map (\z -> toInteger (fst z)) 
                        (filter (\x -> (snd x) == i) input)) | i <- [0..10]]
    equal = [validoutput!!i == toInteger (fst (reduceroutput!!i)) | 
              i <- [0..10]]
-- 
-- -- Generate infinite list of numbers between 1 and 'x'
-- randX :: Integer -> [Integer]   
-- randX x = randomRs (1,x) (unsafePerformIO newStdGen)
-- 
-- -- Generate random lists of indexes
-- randindex 15 i = randindex 1 i
-- randindex m i = (P.take n (repeat i)) P.++ (randindex (m+1) (i+1))
--   where
--     [n] = P.take 1 rnd
--     rnd = randomRs (1,m) (unsafePerformIO newStdGen)
-- 
-- -- Combine indexes and values to generate random input for the reducer    
-- randominput n x = P.zip data_in index_in 
--   where
--     data_in   = P.map (fromInteger :: Integer -> DataInt) (P.take n (randX x))
--     index_in  = P.map (fromInteger :: Integer -> ArrayIndex)
--                         (P.take n (randindex 7 0))
-- main = 
--   do
--     putStrLn (show runReducer)

-- simulate f input s = do
--   putStr "Input: "
--   putStr $ show input
--   putStr "\nInitial State: "
--   putStr $ show s
--   putStr "\n\n"
--   foldl1 (>>) (map (printOutput) output)
--   where
--     output = run f input s

initstate :: ReducerState
initstate = State
  ( State ( (255 :: ArrayIndex)
    , (7 :: SizedWord DiscrSize)
    )
  , State ( copy ((0::DataInt,0::Discr),Low)
    , (2 :: RangedWord AdderDepth)
    )
  , State (copy ((0::DataInt,0::Discr),Low))
  , State ( State (copy (0::DataInt))
          , State (copy (0::DataInt))
          , State (copy (0::ArrayIndex))
          , (copy Low)
          )
  )

{-# ANN siminput TestInput #-}
siminput :: [(DataInt, ArrayIndex)]
siminput =  [(13,0)::(DataInt, ArrayIndex),(7,0)::(DataInt, ArrayIndex),(14,0)::(DataInt, ArrayIndex),(14,0)::(DataInt, ArrayIndex),(12,0)::(DataInt, ArrayIndex),(10,0)::(DataInt, ArrayIndex),(19,1)::(DataInt, ArrayIndex),(20,1)::(DataInt, ArrayIndex),(13,1)::(DataInt, ArrayIndex)
            ,(5,1)::(DataInt, ArrayIndex),(9,1)::(DataInt, ArrayIndex),(16,1)::(DataInt, ArrayIndex),(15,1)::(DataInt, ArrayIndex),(10,2)::(DataInt, ArrayIndex),(13,2)::(DataInt, ArrayIndex),(3,2)::(DataInt, ArrayIndex),(9,2)::(DataInt, ArrayIndex),(19,2)::(DataInt, ArrayIndex),(5,3)::(DataInt, ArrayIndex)
            ,(5,3)::(DataInt, ArrayIndex),(10,3)::(DataInt, ArrayIndex),(17,3)::(DataInt, ArrayIndex),(14,3)::(DataInt, ArrayIndex),(5,3)::(DataInt, ArrayIndex),(15,3)::(DataInt, ArrayIndex),(11,3)::(DataInt, ArrayIndex),(5,3)::(DataInt, ArrayIndex),(1,3)::(DataInt, ArrayIndex),(8,4)::(DataInt, ArrayIndex)
            ,(20,4)::(DataInt, ArrayIndex),(8,4)::(DataInt, ArrayIndex),(1,4)::(DataInt, ArrayIndex),(11,4)::(DataInt, ArrayIndex),(10,4)::(DataInt, ArrayIndex),(13,5)::(DataInt, ArrayIndex),(18,5)::(DataInt, ArrayIndex),(5,5)::(DataInt, ArrayIndex),(6,5)::(DataInt, ArrayIndex),(6,5)::(DataInt, ArrayIndex)
            ,(4,6)::(DataInt, ArrayIndex),(4,6)::(DataInt, ArrayIndex),(11,6)::(DataInt, ArrayIndex),(11,6)::(DataInt, ArrayIndex),(11,6)::(DataInt, ArrayIndex),(1,6)::(DataInt, ArrayIndex),(11,6)::(DataInt, ArrayIndex),(3,6)::(DataInt, ArrayIndex),(12,6)::(DataInt, ArrayIndex),(12,6)::(DataInt, ArrayIndex)
            ,(2,6)::(DataInt, ArrayIndex),(14,6)::(DataInt, ArrayIndex),(11,7)::(DataInt, ArrayIndex),(13,7)::(DataInt, ArrayIndex),(17,7)::(DataInt, ArrayIndex),(9,7)::(DataInt, ArrayIndex),(19,8)::(DataInt, ArrayIndex),(4,9)::(DataInt, ArrayIndex),(18,10)::(DataInt, ArrayIndex)
            ,(6,10)::(DataInt, ArrayIndex),(18,11)::(DataInt, ArrayIndex),(1,12)::(DataInt, ArrayIndex),(3,12)::(DataInt, ArrayIndex),(14,12)::(DataInt, ArrayIndex),(18,12)::(DataInt, ArrayIndex),(14,12)::(DataInt, ArrayIndex),(6,13)::(DataInt, ArrayIndex)
            ,(9,13)::(DataInt, ArrayIndex),(11,14)::(DataInt, ArrayIndex),(4,14)::(DataInt, ArrayIndex),(1,14)::(DataInt, ArrayIndex),(14,14)::(DataInt, ArrayIndex),(14,14)::(DataInt, ArrayIndex),(6,14)::(DataInt, ArrayIndex),(11,15)::(DataInt, ArrayIndex)
            ,(13,15)::(DataInt, ArrayIndex),(7,15)::(DataInt, ArrayIndex),(2,16)::(DataInt, ArrayIndex),(16,16)::(DataInt, ArrayIndex),(17,16)::(DataInt, ArrayIndex),(5,16)::(DataInt, ArrayIndex),(20,16)::(DataInt, ArrayIndex),(17,16)::(DataInt, ArrayIndex)
            ,(14,16)::(DataInt, ArrayIndex),(18,17)::(DataInt, ArrayIndex),(13,17)::(DataInt, ArrayIndex),(1,17)::(DataInt, ArrayIndex),(19,18)::(DataInt, ArrayIndex),(1,18)::(DataInt, ArrayIndex),(20,18)::(DataInt, ArrayIndex),(4,18)::(DataInt, ArrayIndex)
            ,(5,19)::(DataInt, ArrayIndex),(4,19)::(DataInt, ArrayIndex),(6,19)::(DataInt, ArrayIndex),(19,19)::(DataInt, ArrayIndex),(4,19)::(DataInt, ArrayIndex),(3,19)::(DataInt, ArrayIndex),(7,19)::(DataInt, ArrayIndex),(13,19)::(DataInt, ArrayIndex),(19,19)::(DataInt, ArrayIndex)
            ,(8,19)::(DataInt, ArrayIndex)
            ]
