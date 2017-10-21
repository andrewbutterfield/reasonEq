{- =============================================================================
 We explore different ways to ensure that a map (a -> Set a)
 is acyclic.

 We use Data.Set and Data.Map rather than lists
 as these already have some efficiencies.
-}
module Acyclic where

import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Time

{- -----------------------------------------------------------------------------

 Introduction

 We have an endo-relation, represented as a set-valued map

-}

type Rel a = Map a (Set a)

rext :: Ord a => a -> Set a -> Rel a -> Rel a
rext a bs m = M.insertWith (S.union) a bs m

rlkp :: Ord a => Rel a -> a -> Set a
rlkp m a
 = case M.lookup a m of
     Nothing  ->  S.empty
     Just bs  ->  bs

{-

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
ins0 a bs m  =   return $ rext a bs m

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
 where m' = rext a bs m

{- ---------------

  Transitive Closure Acyclic Check

-}
transCheck :: Ord a => CycChk a
transCheck m  =   all (loopFree m') (M.keys m') where m' = transClose m

loopFree :: Ord a => Rel a -> a -> Bool
loopFree m a = not (a `S.member` rlkp m a)

transClose :: Ord a => Rel a -> Rel a
transClose m = untilSame transStep m

transStep :: Ord a => Rel a -> Rel a
transStep m = foldl keyStep m $ M.keys m

keyStep :: Ord a => Rel a -> a -> Rel a
keyStep m a = foldl (elemStep a) m (rlkp m a)

elemStep :: Ord a => a -> Rel a -> a -> Rel a
elemStep a m b = rext a (rlkp m b) m

untilSame f x
 | x' == x  =  x
 | otherwise  =  untilSame f x'
 where x' = f x

instrans :: Ord a => InsertOp a
instrans = ins1 transCheck

{- ---------------

  Annihilation Acyclic Check

-}
annihilCheck :: Ord a => CycChk a
annihilCheck m  =  annihilate m == M.empty

annihilate :: Ord a => Rel a -> Rel a
annihilate m = untilSame annihilStep m

annihilStep :: Ord a => Rel a -> Rel a
annihilStep m
 = let (nullkeys,livekeys) = M.partition S.null m
       deadends = S.unions (M.elems m) S.\\ (S.fromList (M.keys m))
   in M.map (S.\\ deadends) livekeys

insannihil :: Ord a => InsertOp a
insannihil = ins1 annihilCheck

{- -----------------------------------------------------------------------------

 Approach 2

 Check each insertion on the fly.

 This requires us to compute the reflexive transitive image
 under the relation of each new range element.

-}
ins2 :: Ord a => InsertOp a
ins2 a bs m
 | a `S.member`  rtImage m bs  =  Nothing
 | otherwise                   =  Just $ rext a bs m

-- reflexive, transitive relational image
rtImage :: Ord a => Rel a -> Set a -> Set a
rtImage m bs = untilSame (rrImage m) bs

-- reflexive relation image   rrImage(m,bs) = bs `union` m(bs)
rrImage :: Ord a => Rel a -> Set a -> Set a
rrImage m bs = S.unions (bs:map (rlkp m) (S.toList bs))

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
      | even i  =  lsqr (reverse ilist) ++ lslide ilist
      | otherwise  =  lsqr ilist ++ lslide (reverse ilist)
      where ilist = [0..i]


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

{- ----------

 Test results: run 12noon approx, 20 Oct 2017

 auto parameters : 1,5,10,15,20,25,30,35,40
 insertion order 1 : instrans insannihil ins2
 insertion order 2 : ins2 insannihil instrans

-}

-- insertion order 1
results1
 :: [( Int -- auto parameter
     , Double  -- instrans time
     , Double  -- insannihil time
     , Double  -- ins2 time
    )]
results1raw
 = [ (1,
      0.000112,
      0.000048,
      0.000028)
    , (5,
      0.002986,
      0.00136,
      0.000475)
    , (10,
      0.047842,
      0.021456,
      0.00333)
    , (15,
      0.308326,
      0.13724,
      0.014361)
    , (20,
      1.248041,
      0.566338,
      0.041856)
    , (25,
      3.953532,
      1.746431,
      0.106121)
    , (30,
      10.214037,
      4.609918,
      0.21445)
    , (35,
      23.588404,
      10.417426,
      0.412417)
    , (40,
      49.199608,
      22.036669,
      0.726038) ]

results1 = map rflip results1raw where rflip (n,c,b,a) = (n,a,b,c)
 -- insertion order 2
results2
 :: [( Int -- auto parameter
    , Double  -- ins2 time
    , Double  -- insannihil time
    , Double  -- instrans time
    )]
results2
 = [ (1,
      0.000067,
      0.000046,
      0.00006)
   , (5,
      0.000583,
      0.00139,
      0.002934)
   , (10,
      0.00411,
      0.023827,
      0.048909)
   , (15,
      0.01719,
      0.140304,
      0.311267)
   , (20,
      0.046396,
      0.565989,
      1.266858)
   , (25,
      0.109973,
      1.75481,
      3.999683)
   , (30,
      0.222754,
      4.633371,
      10.208467)
   , (35,
      0.429673,
      10.479945,
      23.554258)
   , (40,
      0.742627,
      21.930164,
      48.449237) ]

rsrender :: [(Int,Double,Double,Double)] -> String
rsrender  = unlines . map rrender
rrender (i,t1,t2,t3) = show i ++ ',':show t1 ++ ',':show t2 ++ ',':show t3

norm (n,a,b,c) = (n,1.0,b/a,c/a)


{-  In CSV form

result 1

1,2.8e-5,4.8e-5,1.12e-4
5,4.75e-4,1.36e-3,2.986e-3
10,3.33e-3,2.1456e-2,4.7842e-2
15,1.4361e-2,0.13724,0.308326
20,4.1856e-2,0.566338,1.248041
25,0.106121,1.746431,3.953532
30,0.21445,4.609918,10.214037
35,0.412417,10.417426,23.588404
40,0.726038,22.036669,49.199608

result 2

1,6.7e-5,4.6e-5,6.0e-5
5,5.83e-4,1.39e-3,2.934e-3
10,4.11e-3,2.3827e-2,4.8909e-2
15,1.719e-2,0.140304,0.311267
20,4.6396e-2,0.565989,1.266858
25,0.109973,1.75481,3.999683
30,0.222754,4.633371,10.208467
35,0.429673,10.479945,23.554258
40,0.742627,21.930164,48.449237

normed result 1

1,1.0,1.7142857142857144,4.0
5,1.0,2.863157894736842,6.286315789473684
10,1.0,6.443243243243243,14.366966966966967
15,1.0,9.556437573985098,21.469674813731633
20,1.0,13.53062882262997,29.817493310397555
25,1.0,16.45697835489677,37.2549448271313
30,1.0,21.496470039636282,47.62899044066216
35,1.0,25.259448567833047,57.19551812849616
40,1.0,30.351949897939228,67.764508193786

normed result 2

1,1.0,0.6865671641791045,0.8955223880597015
5,1.0,2.384219554030875,5.032590051457976
10,1.0,5.797323600973236,11.9
15,1.0,8.16195462478185,18.10744618964514
20,1.0,12.199090438830932,27.305328045521165
25,1.0,15.956734834914023,36.36968164913206
30,1.0,20.80039415678282,45.82843405730088
35,1.0,24.390513250774426,54.81903214770302
40,1.0,29.530523398691404,65.240338689544

-}
