{-# LANGUAGE RecordWildCards #-}

module Main where

import Test.QuickCheck
import qualified Data.Map.Strict as Map

import Prisoners 

-----------------------------------------------------------------------------
-- QUICKCHECK GENERATORS (Replicating TLA+ Init & Next)
-----------------------------------------------------------------------------

-- | Generates an initial state matching the TLA+ 'Init' predicate.
genInitState :: Gen State
genInitState = do
    initA <- arbitrary
    initB <- arbitrary
    return $ State 
        { switchAUp = initA
        , switchBUp = initB
        , timesSwitched = Map.fromList [(i, 0) | i <- [1 .. totalPrisoners - 1]]
        , count = 0
        , timesInterfered = 0
        }

-- | Generates a valid execution trace (a sequence of states) from Init to Done.
-- To prevent infinite loops in tests, we cap the maximum steps at 10,000.
genTrace :: Gen [State]
genTrace = do
    start <- genInitState
    buildTrace start 0
  where
    buildTrace st depth
        | isDone st || depth > 10000 = return [st]
        | otherwise = do
            let actions = enabledActions st
            if null actions 
                then return [st] -- Deadlock state (should not happen in this model)
                else do
                    act <- elements actions
                    wChoice <- arbitrary -- Randomly resolve Warden non-determinism
                    let nextSt = stepPure st act wChoice
                    rest <- buildTrace nextSt (depth + 1)
                    return (st : rest)

-----------------------------------------------------------------------------
-- PROPERTIES TO RUN
-----------------------------------------------------------------------------

-- | PROPERTY 1: TypeOK must be an invariant across all generated execution paths.
prop_TypeOKHolds :: Property
prop_TypeOKHolds = forAll genTrace $ \trace ->
    counterexample "TypeOK invariant violated!" $ all checkTypeOK trace

-- | PROPERTY 2: CountInvariant must hold at every single step of every trace.
prop_CountInvariantHolds :: Property
prop_CountInvariantHolds = forAll genTrace $ \trace ->
    counterexample "CountInvariant violated during execution trace!" $ all checkCountInvariant trace

-- | PROPERTY 3: Safety Property (Spec => Safety)
-- For any trace that successfully reaches 'isDone', the safety predicate must be true.
prop_SafetyHolds :: Property
prop_SafetyHolds = forAll genTrace $ \trace ->
    let finalState = last trace
    in isDone finalState ==> counterexample "Warden released prisoners but someone didn't visit!" (checkSafety finalState)

-----------------------------------------------------------------------------
-- TEST RUNNER (Main Entry Point)
-----------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "--- Running TLA+ Specification Compliance Tests ---"
    
    putStrLn "\n1. Checking Invariant: TypeOK..."
    quickCheckWith stdArgs { maxSuccess = 500 } prop_TypeOKHolds
    
    putStrLn "\n2. Checking Invariant: CountInvariant..."
    quickCheckWith stdArgs { maxSuccess = 500 } prop_CountInvariantHolds
    
    putStrLn "\n3. Checking Theorem: Spec => Safety..."
    quickCheckWith stdArgs { maxSuccess = 500 } prop_SafetyHolds