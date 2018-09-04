\section{Term and Match Ranking}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Ranking
  ( RankFunction, rankAndSort
  , sizeRank )
where

import Data.List (sortOn)
import qualified Data.Set as S

import AST
import Laws
import LiveProofs

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

Ranking matches to show those most likely to be useful.
\begin{code}
type RankFunction = [MatchContext] -> Match -> Int

rankAndSort :: RankFunction -> [MatchContext] -> Matches -> Matches
rankAndSort rf ctxts ms  = map snd $ sortOn fst $ zip (map (rf ctxts) ms) ms
\end{code}

Simple ranking by replacement term size:
\begin{code}
sizeRank :: RankFunction
sizeRank _ m = termSize $ mRepl m

termSize :: Term -> Int
termSize (Val _ _)       = 1
termSize (Var _ _)       = 1
termSize (Cons _ _ ts)   = 1 + sum (map termSize ts)
termSize (Bind _ _ vs t) = 1 + S.size vs + termSize t
termSize (Lam _ _ vl t)  = 1 + length vl + termSize t
termSize (Sub _ t subs)  = 1 + termSize t + subsSize subs
termSize (Iter _ _ _ vl) = 3 + length vl
termSize (Type _) = 2

subsSize (Substn ts lvs) = 3 * S.size ts + 2 * S.size lvs
\end{code}
