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

type SDAGStats a
  = ( Bool  -- true if domain element already present
    , [a]   -- range elements not present
    , Int ) -- level of highest range element

validateSDAGins :: Eq a => a -> [a] -> SDAG a -> SDAGStats a
validateSDAGins n ns sdag
  = validate n 0 sdag ( False, ns, -1 )

validate :: Eq a => a -> Int -> SDAG a -> SDAGStats a -> SDAGStats a
validate n currLvl [] res = res
validate n currLvl (lvl:lvls) res
  =  validate' n currLvl lvl res `mrg` validate n (currLvl+1) lvls

validate' :: Eq a => a -> Int -> SDAGLevel a -> SDAGStats a -> SDAGStats a
validate' n currLvl [] res = res
validate' n currLvl ((m,ms):rest) res@(nPresent, ns, highRange)
 | n == m  =  (True,ns,highRange)
 | otherwise = validate' n currLvl rest (nPresent, ns', hR')
 where
   ns' =  ns \\ [m]
   hR' = if highRange == -1 && ns' /= ns then currLvl else highRange

mrg :: SDAGStats a -> (SDAGStats a -> SDAGStats a) -> SDAGStats a
mrg res@(nPresent,_,_) f  =  if nPresent then res else f res

insSDAG :: (Eq a, Monad m) => a -> [a] -> SDAG a -> m (SDAG a)
insSDAG n ns sdag
  = case validateSDAGins n ns sdag of
      (True,_,_)   ->  fail "domain node already present"
      (_,(_:_),_)  ->  fail "some range nodes not present"
      (_,_,-1)     ->  return $ insSDAGbottom n sdag
      (_,_,i)      ->  return $ insSDAGLvl n ns i sdag

insSDAGbottom n []         =  [ [ (n,[]) ] ]
insSDAGbottom n [lvl]      =  [ (n,[]):lvl ]
insSDAGbottom n (lvl:lvls) =  lvl : insSDAGbottom n lvls

insSDAGLvl n ns 0 sdag        =  [(n,ns)]:sdag
insSDAGLvl n ns 1 (lvl:lvls)  =  ((n,ns):lvl) : lvls
insSDAGLvl n ns i (lvl:lvls)  =  lvl : insSDAGLvl n ns (i-1) lvls

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




{-
Test examples.
-}

-- well-formed
sdag0 = []
sdag1 = [ [ (1,[]) ] ]
sdag2 = [ [ (2,[]), (1,[]) ] ]
sdag3 = [ [ (3,[1,2]) ]
        , [ (2,[]), (1,[]) ]
        ]
sdag4 = [ [ (4,[1,3]) ]
        , [ (3,[1,2]) ]
        , [ (2,[]), (1,[]) ]
        ]
