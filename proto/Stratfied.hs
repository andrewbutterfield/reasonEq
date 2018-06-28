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

 Key idea: stratified lists
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

{-
 Extracting a node and all its dependencies, ordered by layer.
-}

extractDeps :: Eq a => a -> SDAG a -> [a]
extractDeps n sdag
  = case findNode n sdag of
      (False, _,  _    )  ->  []
      (True,  ns, sdag')  -> findDeps n [] ns sdag'

findNode :: Eq a => a -> SDAG a ->  ( Bool, [a], SDAG a )
findNode n []          =  ( False, [], [] )
findNode n (lvl:lvls)  =  findNode' n lvls lvl

findNode' n lvls []    =  findNode n lvls
findNode' n lvls ((m,ms):rest)
 | n == m              =  ( True, ms, lvls )
 | otherwise           =  findNode' n lvls rest

findDeps :: Eq a => a -> [a] -> [a] -> SDAG a -> [a]
findDeps n sped []  _  =  n : reverse sped
findDeps n sped ns  []  =  []
findDeps n sped ns (lvl:lvls) = findDeps' n sped ns lvls lvl

findDeps' n sped [] _ _ = n : reverse sped
findDeps' n sped ns lvls [] = findDeps n sped ns lvls
findDeps' n sped ns lvls ((m,ms):rest)
  | m `elem` ns  =  findDeps' n (m:sped) (nub (ms ++ (ns \\ [m]))) lvls rest
  | otherwise    =  findDeps' n    sped          ns                lvls rest



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
