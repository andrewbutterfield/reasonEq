\section{Term and Match Ranking}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Ranking
  ( Rank, RankFunction
  , rankAndSort
  , sizeRank
  , isNonTrivial, nonTrivialSizeRank
  , nonTrivialQuantifiers
  )
where

import Data.List (sortOn)
import qualified Data.Set as S

import AST
import Binding
import Laws
import Proofs
import Instantiate
import LiveProofs

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\subsection{Ranking Types}

Ranking matches to show those most likely to be useful.
\begin{code}
type Rank = Int -- the lower, the better
type RankFunction = [MatchContext] -> Match -> Rank
type FilterFunction = [MatchContext] -> Match -> Bool
\end{code}

\subsection{Ranking Match Lists}

Simple sorting according to rank,
with duplicate replacements removed.
\begin{code}
rankAndSort :: RankFunction -> [MatchContext] -> Matches -> Matches
rankAndSort rf ctxts ms
  =  remDupRepl $ map snd $ sortOn fst $ zip (map (rf ctxts) ms) ms
remDupRepl []       =  []
remDupRepl one@[_]  =  one
remDupRepl (m1:rest@(m2:ms))
  | sameRepl m1 m2  =       remDupRepl (m1:ms)
  | otherwise       =  m1 : remDupRepl rest

sameRepl :: Match -> Match -> Bool
sameRepl m1 m2 = mRepl m1 == mRepl m2
\end{code}


\newpage
\subsection{Size Matters}

Simple ranking by replacement term size,
after the binding is applied:
\begin{code}
sizeRank :: RankFunction
sizeRank _ m
 = case instantiate (mBind m) replL of
    Just replC  ->  termSize replC
    -- instantiate fails if some variables not bound (?v)
    -- rank these as 'larger'
    Nothing     ->  10 * termSize replL
 where replL = mRepl m

termSize :: Term -> Int
termSize (Val _ _)            =  1
termSize (Var _ _)            =  1
termSize (Cons _ _ _ ts)      =  1 + sum (map termSize ts)
termSize (Bnd _ _ vs t)       =  1 + S.size vs + termSize t
termSize (Lam _ _ vl t)       =  1 + length vl + termSize t
termSize (Cls _ t)            =  1 + termSize t
termSize (Sub _ t subs)       =  1 + termSize t + subsSize subs
termSize (Iter _ _ _ _ _ vl)  =  3 + length vl
termSize (Typ _)              =  2

subsSize (Substn ts lvs)      =  3 * S.size ts + 2 * S.size lvs
\end{code}

\subsection{Penalise Trivial Matches}


\subsubsection{Filter}

Ranking by term size,
but where being trivial has a very high penalty
\begin{code}
isNonTrivial :: Match -> Bool
isNonTrivial m
  =  nontrivial $ mClass m
  where
     nontrivial (MatchEqvVar _)  =  False
     nontrivial _                =  True
\end{code}

\subsubsection{Ranking}

\begin{code}
trivialHit = 1000000

trivialPenalty :: Match -> Int
trivialPenalty m
  | isNonTrivial m  =  0
  | otherwise       =  trivialHit

nonTrivialSizeRank :: RankFunction
nonTrivialSizeRank mctxts m
 = sizeRank mctxts m + trivialPenalty m
\end{code}


\subsection{Drop Vanishing Quantifiers}

Often we do not want matches in which all pattern list-variables
are mapped to empty sets and lists.

\begin{code}
nonTrivialQuantifiers :: FilterFunction
nonTrivialQuantifiers _  =  not . onlyTrivialQuantifiers . mBind
\end{code}
