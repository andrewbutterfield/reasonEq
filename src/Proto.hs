{- =============================================================================
 We explore different ways to ensure that a map (a -> Set a)
 is acyclic.

 We use Data.Set and Data.Map rather than lists
 as these already have some efficiencies.
-}
module Proto where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Time

type Rel a = Map a (Set a)

{- -----------------------------------------------------------------------------

 Introduction

 We consider how we might ensure that the operation
 insert a bs m  does not result in a cycle.
 We want that it has good performance.
 In effect we want the insert operation to visibly fail
 if it would result in a cycle.
-}
type InsertOp a = a -> Set a -> Rel a -> Maybe (Rel a)

{- -----------------------------------------------------------------------------

 Approach 0

 An insertion that does no checks, for speed reference,
 as well as one that doesn't insert!

-}
ins0 :: Ord a => InsertOp a
ins0 a bs m  =   return $ M.insertWith (S.union) a bs m

insx :: Ord a => InsertOp a
insx a bs m = return m

{- -----------------------------------------------------------------------------

 Approach 1

 Do the insert, then check result for cycles.
 We will explore two cycle-check algorithms
 (transitive closure vs. annihilation),
 so we make that algorithm a parameter

-}
type CycChk a = Rel a -> Bool

ins1 :: Ord a => CycChk a -> InsertOp a
ins1 chk a bs m
 | chk m'  =  return m'
 | otherwise  =  fail "ins1: cycle!"
 where m' = M.insertWith (S.union) a bs m

{- -----------------------------------------------------------------------------

 Approach 2

 Check each insertion on the fly.

-}
ins2 :: Ord a => InsertOp a
ins2 a bs m  =  error "ins2: NYI"


{- -----------------------------------------------------------------------------

 Performance

 We want a big test that builds a big map with failures along the way
 so we can get good benchmarks

-}
type AddTst a = (a, Set a)

type Test a = [AddTst a] -> InsertOp a -> Rel a

runtest :: Ord a => Test a
runtest tests ins  = run ins M.empty $! tests

run ins m [] = m
run ins m ((a,bs):tests)
 = case ins a bs m of
     Nothing  ->  run ins m tests
     Just m'  ->  run ins m' tests

{- ----------

    Test generator

    Want to generate a lot of tests with a significant proportion of bad inserts
    that has a large final result.
-}

-- some quick shorthands
emp = S.empty
sngl = S.singleton
set :: Ord a => [a] -> Set a
set = S.fromList

{-
   auto-generate, with increasing size s = 0..n

-}
lsqr :: Ord a => [a] -> [(a,Set a)]
lsqr as = concat $ map (tag as) as
 where tag as a = map (pair a) as
       pair a b = (a,sngl b)

lslide :: Ord a => [a] -> [(a,Set a)]
lslide as = lslide' [] as
 where
   lslide' _ [] = []
   lslide' as (b:cs) = (b,set (as++cs)) : lslide' (b:as) cs

auto n
  = concat $ map gen [0..n]
  where
    gen i
      = lsqr ilist ++ lslide ilist
      where ilist = reverse [0..i]


{- ----------

   Test Harness

   We take a test and list of inserts and run them with timing.

-}
timedtests inss tests
 = mapM_ (dotimedtest tests) inss
 where
    dotimedtest tests ins
      = do start <- getCurrentTime
           return $! runtest tests ins
           stop <- getCurrentTime
           print $ diffUTCTime stop start



{-
Import Data.Time
...
   start <- getCurrentTime
   runOperation
   stop <- getCurrentTime
   print $ diffUTCTime stop start

-}
