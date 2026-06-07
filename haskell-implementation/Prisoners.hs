{-# LANGUAGE RecordWildCards #-}

module Prisoners 
    ( State(..)
    , Action(..)
    , totalPrisoners
    , maxInterferences
    , isDone
    , checkSafety
    , checkCountInvariant
    , checkTypeOK
    , enabledActions
    , stepPure
    , initState
    , simulate
    , main
    ) where

import qualified Data.Map.Strict as Map
import System.Random (randomIO, randomRIO)
import Control.Monad (when, unless)

-----------------------------------------------------------------------------
-- CONSTANTS
-----------------------------------------------------------------------------

totalPrisoners :: Int
totalPrisoners = 10 

maxInterferences :: Int
maxInterferences = 3 

-----------------------------------------------------------------------------
-- VARIABLES (State)
-----------------------------------------------------------------------------

data State = State 
    { switchAUp       :: Bool
    , switchBUp       :: Bool
    , timesSwitched   :: Map.Map Int Int  -- Map from NonCounter prisoner ID to count
    , count           :: Int              -- Counter's count
    , timesInterfered :: Int              -- Warden's interference count
    } deriving (Show, Eq)

data Action = CounterAction | NonCounterAction Int | WardenAction deriving (Show, Eq)

-----------------------------------------------------------------------------
-- THEOREMS & INVARIANTS (Verification)
-----------------------------------------------------------------------------

isDone :: State -> Bool
isDone State{..} = 
    count == (maxInterferences + 2) * (totalPrisoners - 1) - maxInterferences

checkSafety :: State -> Bool
checkSafety State{..} = 
    all (> 0) (Map.elems timesSwitched)

checkCountInvariant :: State -> Bool
checkCountInvariant State{..} =
    let totalSwitched = sum (Map.elems timesSwitched)
        oneIfUp = if switchAUp then 1 else 0
        cond1 = count <= (totalSwitched - oneIfUp + 1)
        cond2 = count >= (totalSwitched - oneIfUp - timesInterfered)
    in cond1 && cond2

-- | ADDED: Verifies the 'TypeOK' invariant from your TLA+ specification
checkTypeOK :: State -> Bool
checkTypeOK State{..} =
    let validSwitched = all (\v -> v >= 0 && v <= maxInterferences + 2) (Map.elems timesSwitched)
        maxCount = (maxInterferences + 2) * (totalPrisoners - 1) + 1
        validCount = count >= 0 && count <= maxCount
        validWarden = timesInterfered >= 0 && timesInterfered <= maxInterferences
    in validSwitched && validCount && validWarden

-----------------------------------------------------------------------------
-- CORE STATE TRANSITIONS (Pure Next-state relations)
-----------------------------------------------------------------------------

enabledActions :: State -> [Action]
enabledActions State{..} = 
    [CounterAction] ++ 
    map NonCounterAction [1 .. totalPrisoners - 1] ++
    [WardenAction | timesInterfered < maxInterferences && (switchAUp || switchBUp)]

-- | ADDED: The pure state transition engine. 
-- The third parameter (wardenChoice) allows QuickCheck to control non-determinism.
stepPure :: State -> Action -> Bool -> State
stepPure st@State{..} action wardenChoice = case action of
    
    CounterAction -> 
        if switchAUp 
        then st { switchAUp = False, count = count + 1 }
        else st { switchBUp = not switchBUp }
        
    NonCounterAction i -> 
        let flipped = Map.findWithDefault 0 i timesSwitched
        in if not switchAUp && flipped < maxInterferences + 2
           then st { switchAUp = True
                  , timesSwitched = Map.insert i (flipped + 1) timesSwitched }
           else st { switchBUp = not switchBUp }
           
    WardenAction -> 
        let flipA = st { switchAUp = False, timesInterfered = timesInterfered + 1 }
            flipB = st { switchBUp = False, timesInterfered = timesInterfered + 1 }
        in if switchAUp && switchBUp 
           then if wardenChoice then flipA else flipB
           else if switchAUp then flipA else flipB

-----------------------------------------------------------------------------
-- SIMULATION LOOP & IO INTERFACE
-----------------------------------------------------------------------------

initState :: IO State
initState = do
    initA <- randomIO
    initB <- randomIO
    return $ State 
        { switchAUp = initA
        , switchBUp = initB
        , timesSwitched = Map.fromList [(i, 0) | i <- [1 .. totalPrisoners - 1]]
        , count = 0
        , timesInterfered = 0
        }

-- | MODIFIED: Relies entirely on stepPure to execute mutations safely
applyAction :: State -> Action -> IO State
applyAction st action = case action of
    WardenAction -> do
        choice <- randomIO :: IO Bool
        return $ stepPure st action choice
    _ -> 
        return $ stepPure st action True

simulate :: State -> Int -> IO (State, Int)
simulate st steps = do
    unless (checkCountInvariant st) $
        error $ "Invariant violated at step " ++ show steps ++ ":\n" ++ show st

    if isDone st
    then return (st, steps)
    else do
        let actions = enabledActions st
        idx <- randomRIO (0, length actions - 1)
        nextSt <- applyAction st (actions !! idx)
        simulate nextSt (steps + 1)

main :: IO ()
main = do
    putStrLn "Initializing Prisoners Puzzle Simulation (TLA+ Spec)..."
    putStrLn $ "Prisoners: " ++ show totalPrisoners ++ ", Max Interferences: " ++ show maxInterferences
    
    startState <- initState
    (finalState, steps) <- simulate startState 0
    
    putStrLn $ "\nSimulation Finished in " ++ show steps ++ " steps."
    putStrLn "Final State:"
    putStrLn $ "  Count: " ++ show (count finalState)
    putStrLn $ "  Warden Interferences: " ++ show (timesInterfered finalState)
    
    let safetyPassed = checkSafety finalState
    putStrLn $ "\nSafety Property Passed (Everyone visited)? " ++ show safetyPassed
    
    if safetyPassed 
       then putStrLn "SUCCESS: The prisoners go free!"
       else putStrLn "FAILURE: The counter guessed wrong!"