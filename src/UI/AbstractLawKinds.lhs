\chapter{Abstract Law-Kinds}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2025
 
LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.AbstractLawKinds
( applyCLA
, tryUnfoldHere, trySimpHere, tryFoldHere
, tryChildren
)
where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Char
import Data.Maybe
import Data.List
import Control.Applicative

import NotApplicable
import YesBut
import Utilities
import UnivSets
import LexBase
import Variables
import SideCond
import Assertions
import Laws
import TermZipper
import Types
import AST
import FreeVars
import AlphaEquiv
import Substitution
import Binding
import VarData
import MatchContext
import Typing
import Instantiate
import Sequents
import ProofSettings
import REqState
import Persistence
import ProofMatch
import Ranking
import Classifier
import SAT
import UI.AbstractProver

import TestRendering
import SourceHandling

import StdTypeSignature

import Debugger
\end{code}

\section{Introduction}

This module provides the abstract functions for implementing automated proving 
based on law classifications (\textit{a.k.a.} kinds).

The overall task breaks down into two main components:
\begin{itemize}
    \item 
      The first implements taking a law 
      and searching through the current proof goal 
      to find a sub-term to which it applies (if any).
    \item 
      The second is about having various collections of laws, 
      grouped by kinds, 
      and how to automate their use in some systematic way 
      to make progress in proofs.
\end{itemize}

\section{Basic Abstract Steps}

\textbf{NOTE: This module cannot import anything from the xxxTUI modules, 
and should not bring in anything from AbstractTop either.}


\begin{verbatim}
moveFocusDown :: MonadFail m => Int -> LiveProof -> m LiveProof
moveFocusUp :: MonadFail m => LiveProof -> m LiveProof

matchFocusAgainst :: MonadFail m => String -> LiveProof -> m LiveProof

applyMatchToFocus1 :: MonadFail m => 
  Int -> LiveProof -> m (ProofMatch,[Variable],[Term],[ListVar],VarList)

applyMatchToFocus2 :: MonadFail m => 
  [VarTable] -> ProofMatch ->
  [(Variable,Term)] -> [(ListVar,VarList)] -> VarList -> 
  LiveProof -> m LiveProof
\end{verbatim}
Function \h{applyMatchToFocus1} is run first,
then the user may be asked to make some choices,
and finally \h{applyMatchToFocus1} is called with the resulting choices.
The overall effect has type 
\verb"MonadFail m => Int -> LiveProof -> m LiveProof".


\section{Abstract Commands}

\textbf{Important:} \emph{Nothing in this module should do IO of any kind}

This is \emph{very} tentative \dots

\section{Top-level Command}
Top level function calls the three functions in turn, passing the resulting liveproof from
the last into the next.
At the end, checks if any progress has been made after all phases have completed.
Returns the modified liveproof if so, otherwise provides failure message.
\begin{code}
applyCLA :: MonadFail mf => ClassifiedLaws -> Ranking -> LiveProof -> mf LiveProof
applyCLA cls ranking lp
  | focus lp3 /= focus lp   = return lp3
  | otherwise               =  fail "applyCLA: no progress"
  where
    lp1          = unfoldEverything   cls ranking lp
    lp2          = simplifyEverything cls ranking lp1
    lp3          = foldEverything     cls ranking lp2
\end{code}
\subsection{Three Phase Approach}
Each of the three phrases do more or less the same thing:
\begin{itemize}
  \item Run (a version of) DFS, trying to apply the relevant operation (unfold, simplify, fold)
at the first node (focus) which succeeds.
  \item If the operation succeeds at any point, the focus is returned to the caller
level (via tryChildren), and the DFS is run again, attempting the same as before
with the new LiveProof.
  \item When the DFS reaches a fixed point, where the operation has not succeeded at 
any node during a singular run of the DFS, then the function returns the current 
LiveProof.
\end{itemize}
The resulting LiveProof may be the same as before the function was called 
if the operation does not succeed anywhere on their first run, otherwise it will be changed.

The focus of the LiveProof is the same as where it was originally called, for
every pass of the DFS, and on return. This is helpful in calling DFS runs from
the same place each time, ensuring changed terms aren't missed, and also helpful
in allowing the overall applyCLA function to return the liveproof at the focus
it was called. 

\subsection{Unfold Phase: Pre-order DFS}
Pre-order (current node, then children) was chosen here as a top down approach reflects a
natural proof strategy of trying to match the largest definition, and unpacking it to find
new children which themselves may be unfolded. 
\textbf{Unfold}: pre-order DFS (try current node before children),
        since unfolding expands the current head into a larger body
        whose children are the ones that next need unfolding.
{Simplify}: post-order DFS (children before current node),
        since inner sub-expressions must reduce before their parent can
        match a simplifier.
  \item \textbf{Fold}: pre-order DFS, since fold patterns tend to be large
        (the full unfolded body); visiting children first risks collapsing
        inner sub-patterns and destroying the outer fold opportunity.
\begin{code}
unfoldEverything :: ClassifiedLaws -> Ranking -> LiveProof -> LiveProof
unfoldEverything cls ranking = preorderFixed
  where
    preorderFixed live = case preorderOnce live of
      Nothing    -> live
      Just live' -> preorderFixed live'
    preorderOnce live
      =   tryUnfoldHere cls ranking live
      <|> tryChildren preorderOnce live
\end{code}

\subsection{Simplify Phase: Post-order DFS}
Post-order (children, then current node) was chosen here to reflect the bottom-up
conventional approach of simplifying leaves before their parents.
\begin{code}
simplifyEverything :: ClassifiedLaws -> Ranking -> LiveProof -> LiveProof
simplifyEverything cls ranking = postorderFixed
  where
    postorderFixed live = case postorderOnce live of
      Nothing    -> live
      Just live' -> postorderFixed live'
    postorderOnce live
      =   tryChildren postorderOnce live
      <|> trySimpHere cls ranking live
\end{code}

\subsection{Fold Phase: Pre-order DFS}
Pre-order (current node, then children) was chosen here to ensure the outermost
patterns can match, preventing pattern destruction by an inner fold.
A limitation of this method is if the simplify phase does not achieve anything,
the fold stage may simply undo everything the unfold stage did, and return to the
LiveProof stage at which the top level command was called (despite having "applied"
a number of laws)
\begin{code}
foldEverything :: ClassifiedLaws -> Ranking -> LiveProof -> LiveProof
foldEverything cls ranking = preorderFixed
  where
    preorderFixed live = case preorderOnce live of
      Nothing    -> live
      Just live' -> preorderFixed live'
    preorderOnce live
      =   tryFoldHere cls ranking live
      <|> tryChildren preorderOnce live
\end{code}

\subsection{Child Traversal}

Tries children 1, 2, 3, \dots\ in order until none exist,
applying \texttt{f} to each and stopping at the first success.
Restores the focus to the caller's level via \texttt{moveFocusUp}.
\begin{code}
tryChildren :: (LiveProof -> Maybe LiveProof) -> LiveProof -> Maybe LiveProof
tryChildren f live = go 1
  where
    go i = case moveFocusDown i live of
      Nothing    -> Nothing
      Just live' -> (f live' >>= moveFocusUp) <|> go (i+1)
\end{code}

\subsection{Per-node Law Attempts}

Try to apply an unfold law (expand definition, LHS$\to$RHS) at the current focus.
\begin{code}
tryUnfoldHere :: ClassifiedLaws -> Ranking -> LiveProof -> Maybe LiveProof
tryUnfoldHere cls ranking lp = do
  lp' <- matchFocus ranking lp
  firstMatchWhere (isUnfoldMatch cls) lp' (zip [1..] (matches lp'))
\end{code}

Try to apply a simplifier at the current focus.
\begin{code}
trySimpHere :: ClassifiedLaws -> Ranking -> LiveProof -> Maybe LiveProof
trySimpHere cls ranking lp = do
  lp' <- matchFocus ranking lp
  firstMatchWhere (isSimpMatch cls) lp' (zip [1..] (matches lp'))
\end{code}

Try to apply a fold (collapse body to definition name, RHS$\to$LHS) at the current focus.
\begin{code}
tryFoldHere :: ClassifiedLaws -> Ranking -> LiveProof -> Maybe LiveProof
tryFoldHere cls ranking lp = do
  lp' <- matchFocus ranking lp
  firstMatchWhere (isFoldMatch cls) lp' (zip [1..] (matches lp'))
\end{code}

Apply the first match satisfying the classifying predicate.
\begin{code}
firstMatchWhere :: (ProofMatch -> Bool) -> LiveProof -> [(Int, ProofMatch)]
                -> Maybe LiveProof
firstMatchWhere _    _   []            = Nothing
firstMatchWhere test lp' ((i,m):rest)
  | test m    = ( do (pm,_,_,_,_) <- applyMatchToFocus1 i lp'
                     applyMatchToFocus2 [] pm [] [] lp' )
                <|> firstMatchWhere test lp' rest
  | otherwise = firstMatchWhere test lp' rest
\end{code}

\subsection{Match Classification Predicates}
The unfold and fold predicates check if the match is both a definition (an element
of the folds list) and applying in the correct direction (left to right for unfold, 
right to left for fold).
The simp predicate check if the match is a simplifier (matches an assertion name in the
list of simplifying assertions and their directions) and if the matching direction fits 
the simplifying direction (is the resulting side smaller).
Both checks are handled by the Classifier's check function and ClassifiedLaws data
structure.  
\begin{code}
isUnfoldMatch :: ClassifiedLaws -> ProofMatch -> Bool
isUnfoldMatch cls m = mName m `elem` folds cls && checkIsUnFold (mClass m)

isSimpMatch :: ClassifiedLaws -> ProofMatch -> Bool
isSimpMatch cls m
  = any (\sd -> fst sd == mName m && checkIsSimp sd (mClass m)) (simps cls)

isFoldMatch :: ClassifiedLaws -> ProofMatch -> Bool
isFoldMatch cls m = mName m `elem` folds cls && checkIsFold (mClass m)
\end{code}

\section{Law Application within a term}

\section{Applying Law Collections}


