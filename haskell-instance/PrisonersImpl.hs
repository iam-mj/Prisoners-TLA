{-# LANGUAGE RecordWildCards #-}

import qualified Data.Map.Strict as Map
import System.Random (randomIO, randomRIO)
import Control.Monad (when)

-----------------------------------------------------------------------------
-- CONSTANTS
-----------------------------------------------------------------------------

-- | Cardinality(Prisoner). Must be > 1.
totalPrisoners :: Int
totalPrisoners = 10 

-- | The number of times the warden can interfere. Must be > 0.
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

-----------------------------------------------------------------------------
-- ACTIONS (Next-state relations)
-----------------------------------------------------------------------------

data Action = CounterAction | NonCounterAction Int | WardenAction deriving (Show, Eq)

-- | The Done predicate: condition that tells the counter everyone has visited.
isDone :: State -> Bool
isDone State{..} = 
    count == (maxInterferences + 2) * (totalPrisoners - 1) - maxInterferences

-- | TypeOK / Init: Generates the initial state with random switch positions.
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

-- | Computes the set of enabled actions in the current state.
-- This corresponds to the \/ (OR) branches in the `Next` relation.
enabledActions :: State -> [Action]
enabledActions State{..} = 
    [CounterAction] ++ 
    map NonCounterAction [1 .. totalPrisoners - 1] ++
    [WardenAction | timesInterfered < maxInterferences && (switchAUp || switchBUp)]

-- | Applies the chosen action to transition to the next state.
applyAction :: State -> Action -> IO State
applyAction st@State{..} action = case action of
    
    -- CounterStep
    CounterAction -> 
        if switchAUp 
        then return st { switchAUp = False, count = count + 1 }
        else return st { switchBUp = not switchBUp }
        
    -- NonCounterStep(i)
    NonCounterAction i -> 
        let flipped = Map.findWithDefault 0 i timesSwitched
        in if not switchAUp && flipped < maxInterferences + 2
           then return st { switchAUp = True
                          , timesSwitched = Map.insert i (flipped + 1) timesSwitched }
           else return st { switchBUp = not switchBUp }
           
    -- WardenStep
    WardenAction -> do
        -- The warden flips switch A down OR switch B down if they are up.
        let flipA = st { switchAUp = False, timesInterfered = timesInterfered + 1 }
        let flipB = st { switchBUp = False, timesInterfered = timesInterfered + 1 }
        
        -- If both are up, the TLA spec uses \/ meaning it's non-deterministic.
        if switchAUp && switchBUp then do
            choice <- randomIO :: IO Bool
            return $ if choice then flipA else flipB
        else if switchAUp then
            return flipA
        else 
            return flipB

-----------------------------------------------------------------------------
-- THEOREMS & INVARIANTS (Verification)
-----------------------------------------------------------------------------

-- | Asserts the Safety condition: If Done is true, everyone has been in the room.
checkSafety :: State -> Bool
checkSafety State{..} = 
    all (> 0) (Map.elems timesSwitched)

-- | Checks the CountInvariant of the Spec.
checkCountInvariant :: State -> Bool
checkCountInvariant State{..} =
    let totalSwitched = sum (Map.elems timesSwitched)
        oneIfUp = if switchAUp then 1 else 0
        cond1 = count <= (totalSwitched - oneIfUp + 1)
        cond2 = count >= (totalSwitched - oneIfUp - timesInterfered)
    in cond1 && cond2

-----------------------------------------------------------------------------
-- SIMULATION LOOP (Fairness)
-----------------------------------------------------------------------------

-- | Simulates the state machine until `Done` is reached.
simulate :: State -> Int -> IO (State, Int)
simulate st steps = do
    -- Continually verify the invariant to ensure our implementation is safe
    when (not $ checkCountInvariant st) $
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