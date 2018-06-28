{- =============================================================================
 We have a DAG implemented as Map n (Set n).
 Entering  n0 |-> { n1,n2,..,nk} into a DAG on succeeds
 if n1,..,nk are already present in its domain.

 Note this means that we can only enter n |-> {} into an empty DAG.

 Given n in DAG, we want to generate a list of n, such that domain
 elements occur before their range elements.
-}
module Stratified where

import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

{- -----------------------------------------------------------------------------

 Introduction

 We have an DAG, represented as a set-valued map
 with an insert as described above.

-}

type DAG a = Map a (Set a)

insDAG :: (Ord a, Monad m) => a -> (Set a) -> DAG a -> m (DAG a)
insDAG n ns dag
 | n `M.member` dag  =  fail "domain node already present"
 | ns `S.isSubsetOf` M.keysSet dag  =  return $ M.insert n ns dag
 | otherwise  =  fail "some range nodes not present"


{- Better idea: stratified lists
      3     [ [ (3,[1,2]) ]
     / \    ,
     1 2      [ (1,[0]), (2,[0]) ]
     \/     ,
     0        [ (0,[]) ] ]
-}

type SDAGEntry a  =  (a,[a])
type SDAGLevel a  =  [SDAGEntry a]
type SDAG a       =  [SDAGLevel a]

lvlDom :: SDAGLevel a -> [a]
lvlDom lvl = map fst lvl

lvlRng :: SDAGLevel a -> [a]
lvlRng lvl = concat $ map snd lvl

issubset :: Eq a => [a] -> [a] -> Bool
xs `issubset` ys  =  null (xs \\ ys)

inLvlDom :: Eq a => a -> SDAGLevel a -> Bool
n `inLvlDom` level = n `elem` lvlDom level

withinLvlDom :: Eq a => [a] -> SDAGLevel a -> Bool
ns `withinLvlDom` level = ns `issubset` lvlDom level

withinLvlRng :: Eq a => [a] -> SDAGLevel a -> Bool
ns `withinLvlRng` level = ns `issubset` lvlRng level

sdagDOM :: SDAG a -> [a]
sdagDOM sdag = concat $ map lvlDom sdag

inSDAGDom :: Eq a => a -> SDAG a -> Bool
n `inSDAGDom` sdag = n `elem`  sdagDOM sdag

insSDAG :: (Eq a, Monad m) => a -> [a] -> SDAG a -> m (SDAG a)

insSDAG n [] []  = return [ [ (n,[]) ] ]
insSDAG n ns []  =  fail "no range nodes present"

insSDAG n [] [level0]
 | n `inLvlDom` level0  =  fail "domain node already present"
 | otherwise            =  return [(n,[]):level0]
insSDAG n ns [level0]
 | n `inLvlDom` level0  =  fail "domain node already present"
 | ns `withinLvlDom` level0 = return [ [ (n,ns)], level0 ]
 | otherwise  =  fail "some range nodes not present"

insSDAG n ns (lvl2:lvl1:lvls) = error "not sure what to do here!"
