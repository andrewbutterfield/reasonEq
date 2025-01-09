\section{Stratified DAGs}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module StratifiedDAG (
  SDAGEntry, SDAGLevel, SDAG
, insSDAG
, lkpSDAG
, getSDAGdeps
, topDownSDAG, bottomUpSDAG
)
where

import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Utilities
\end{code}

\subsection{Introduction}

We have a directed acyclic graph (DAG)
implemented as $\delta : N \fun \power N$.
We require that entering  $n_0 \mapsto \{n_1,n_2,\dots,n_k\}$ into a DAG
only succeeds if $n_0$ is not already present
and $n_1,..,n_k$ are already present, in its domain.
Note this means that we can only enter
$n \mapsto \emptyset$ into an empty DAG.

\subsection{Types}


Given $n \in \dom\delta$, we want to generate a list of all nodes
reachable from $n$, such that domain
elements occur before their range elements.

Key idea: represent as stratified lists.
\begin{verbatim}
            [
      3        [ (3,[1,2]) ]
     / \    ,
     1 2       [ (1,[0]), (2,[0]) ]
     \ /    ,
      0        [ (0,[]) ]
            ]
\end{verbatim}
\begin{code}
type SDAGEntry a  =  (a,[a])
type SDAGLevel a  =  [SDAGEntry a]
type SDAG a       =  [SDAGLevel a]
\end{code}

\subsection{SDAG Lookup}

\begin{code}
lkpSDAG :: (Eq a, MonadFail m) => a -> SDAG a -> m [a]
lkpSDAG _ [] = fail "not found"
lkpSDAG n (lvl:lvls) = lkpSDAG' n lvls lvl

lkpSDAG' n lvls [] = lkpSDAG n lvls
lkpSDAG' n lvls ((m,ms):rest)
 | n == m  =  return ms
 | otherwise  =  lkpSDAG' n lvls rest
\end{code}

\subsection{SDAG Insertion}

\subsubsection{Insertion pre-condition}

\begin{code}
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
\end{code}

\subsubsection{Insertion}

\begin{code}
insSDAG :: (Eq a, Show a, MonadFail m)
        => String -> String -> a -> [a] -> SDAG a
        -> m (SDAG a)
insSDAG domain range n ns sdag
  = case validateSDAGins n ns sdag of
      (True,_,_)   ->  fail (domain++" already present")
      (_,stuff@(_:_),_)  ->  fail ("missing "++range++" "++show stuff)
      (_,_,-1)     ->  return $ insSDAGbottom n sdag
      (_,_,i)      ->  return $ insSDAGLvl n ns i sdag

insSDAGbottom n []         =  [ [ (n,[]) ] ]
insSDAGbottom n [lvl]      =  [ (n,[]):lvl ]
insSDAGbottom n (lvl:lvls) =  lvl : insSDAGbottom n lvls

insSDAGLvl n ns 0 sdag        =  [(n,ns)]:sdag
insSDAGLvl n ns 1 (lvl:lvls)  =  ((n,ns):lvl) : lvls
insSDAGLvl n ns i (lvl:lvls)  =  lvl : insSDAGLvl n ns (i-1) lvls
\end{code}

\newpage
\subsection{Dependency extraction}

Extracting a node and all its dependencies, ordered by layer.
\begin{code}
getSDAGdeps :: Eq a => a -> SDAG a -> [a]
getSDAGdeps n sdag
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
  | otherwise    =  findDeps' n    sped               ns           lvls rest
\end{code}

Listing all nodes in dependency order (top-down, and bottom-up)
\begin{code}
topDownSDAG :: SDAG a -> [a]  -- type SDAG a = [[(a,[a])]]
topDownSDAG = concat . map (map fst)

bottomUpSDAG :: SDAG a -> [a]
bottomUpSDAG = reverse . topDownSDAG
\end{code}

\subsection{Misc. stuff}

\begin{code}
lvlDom :: SDAGLevel a -> [a]
lvlDom lvl = map fst lvl

lvlRng :: SDAGLevel a -> [a]
lvlRng lvl = concat $ map snd lvl

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
\end{code}

\newpage
\subsection{Test examples}

\begin{code}
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
\end{code}
