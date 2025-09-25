\chapter{Term and Match Ranking}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017--25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Ranking
  ( FilterFunction, OrderFunction, Ranking
  , filterAndSort -- used in ProverTUI
  -- exported Filters
  , acceptAll, acceptNone -- used in ProofSettings
  , isTrivialMatch-- used in ProofSettings
  , onlyTrivialLVarMatches -- used in ProofSettings
  , anyTrivialSubstitutions -- used in ProofSettings
  , hasFloatingVariables -- used in ProofSettings
  -- exported Orderings
  , sizeOrd -- not used
  , favourDefLHSOrd -- used in ProverTUI
  -- exported rankings
  , sizeRanking -- not used
  , favouriteRanking -- not used
  )
where

import Data.List (sortOn)
import qualified Data.Set as S

import Utilities
import Variables
import AST
import Binding
import Laws
import Proofs
import Instantiate
import MatchContext
import ProofMatch
import TestRendering

import Debugger
mtdbg msg mtchs = trc (msg++":\n"++unlines (map mdetails mtchs)) mtchs
mdetails mtch
   = mName mtch
     ++ " @ " ++ showMatchClass (mClass mtch)
     ++ " -->  " ++ trTerm 0 (mRepl mtch)
\end{code}

\section{Ranking Types}

Ranking involves two phases: filtering, and ordering.
Filtering is using a predicate to decide what matches to consider
for ranking.
Ordering is done by computing a $n$-tuple of values ($n \geq 1$),
to be used in sorting comparisons.
The values should belong to a type that has an instance of \texttt{Ord},
so that the tuple itself is also an instance of \texttt{Ord}.
\begin{code}
type FilterFunction = [MatchContext] -> ProofMatch -> Bool
type OrderFunction ord = [MatchContext] -> ProofMatch -> ord
type Ranking = [MatchContext] -> Matches -> Matches
\end{code}

\section{Ranking Match Lists}

Simple sorting according to rank,
with duplicate replacements removed
(this requires us to instantiate the replacements).

\begin{code}
filterAndSort :: Ord ord
              => (FilterFunction, OrderFunction ord) -> [MatchContext]
              -> Matches -> Matches
filterAndSort (ff,rf) ctxts ms
  = let fms = filter (ff ctxts) $ ldbg mshow "fAS.ms" ms
    in remDupRepl $ map snd $ sortOn fst $ zip (map (rf ctxts) fms) $ ldbg mshow "fAS.fms" fms
  where  
    mshow m = 
      mName m 
      ++ "(" 
      ++ show (mClass m)
      ++ ")  --  "
      ++ trTerm 0 (mRepl m)
\end{code}

Note: given the same instantiated replacement from different laws,
we want the most general law, 
which is found in the theory furthest down the theory SDAG
(closest to \h{Equiv}).
We do this because ``lower'' theories are more stable so lessening the risk
that the proof will break%
\footnote{
 This will only matter when we get to the point of replaying proofs to check them
 }%
.
\begin{code}
remDupRepl :: Matches -> Matches
remDupRepl []       =  []
remDupRepl [m]  =  [m]
remDupRepl (m1:rest@(m2:ms))
  | sameRepl m1 m2  =       remDupRepl (m2:ms) -- prefer "earlier" laws
  | otherwise       =  m1 : remDupRepl rest

sameRepl :: ProofMatch -> ProofMatch -> Bool
sameRepl m1 m2 = mRepl m1 == mRepl m2
\end{code}

\section{Rankings}


\subsection{Size Matters}

\begin{code}
sizeRanking :: Ranking
sizeRanking = filterAndSort ( acceptAll, sizeOrd )
\end{code}

\subsection{No Vanishing Q, favour LHS}

\begin{code}
favouriteRanking  :: Ranking
favouriteRanking = filterAndSort ( onlyTrivialLVarMatches, favourDefLHSOrd )
\end{code}


\newpage
\section{Filters}

\subsection{Accept All/None}

\begin{code}
acceptAll, acceptNone :: FilterFunction
acceptAll _ _   =  True
acceptNone _ _  =  False
\end{code}

\subsection{Accept Floating Matches}

Some matches to one part of a law will not cover all the variables
in the other (replacement) part.
Sometimes we need these matches, sometimes they are a distraction.
\begin{code}
hasFloatingVariables :: FilterFunction
hasFloatingVariables _ =   any isFloatingGVar . mentionedVars . mRepl
\end{code}


\subsection{Pathological Cases}

Some matches are quite pathological in character,
and usually we want to supress these.
Sometimes, however, they are useful.

We provide some predicates here that identify specific pathologies.

\subsubsection{Trivial Matches}

Matches against a single predicate variable
\begin{code}
isTrivialMatch :: FilterFunction
isTrivialMatch _ m
  = trivial $ pdbg "isTvlMtch.mClass" $ mClass m
  where
     trivial (MatchEqvVar _)  =  True
     trivial _                =  False
\end{code}

\subsubsection{Vanishing List Variables}

All pattern list-variables
are mapped to empty sets or lists.
\begin{code}
onlyTrivialLVarMatches :: FilterFunction
onlyTrivialLVarMatches _ mtch
  =  onlyTrivialListVarBindings (pdbg "onlyTLV.mBind" $ mBind mtch)
\end{code}

\subsubsection{Accept Empty Substitutions}

Matches that contain empty substitutions ($t[/]$).
\begin{code}
anyTrivialSubstitutions :: FilterFunction
anyTrivialSubstitutions _  =  anyTrivialSubstitution . mRepl
\end{code}


\newpage
\section{Orderings}

In orderings, smaller is better.

\subsection{Term Size}

Simple ranking by replacement term size,
after the binding is applied:
\begin{code}
sizeOrd :: OrderFunction Int
sizeOrd _ m  =  termSize $ mRepl m
\end{code}


\subsection{Favour LHS and Definitions}

Show matches to laws named as definitions first,
then those matching LHS of equivalence laws,
and then the rest.
\begin{code}
favourDefLHSOrd :: OrderFunction (Int,Int,Int)
favourDefLHSOrd ctxt m
  = ( subMatchDef $ mName m
    , subMatchOrd $ mClass m
    , sizeOrd ctxt m
    )

subMatchDef :: String -> Int
subMatchDef lawname
 | take 4 (reverse lawname) == "fed_"  =  0
 | otherwise                           =  1

subMatchOrd :: MatchClass -> Int
subMatchOrd MatchAll         =  0
subMatchOrd MatchEqvLHS      =  1
subMatchOrd MatchEqvRHS      =  2
subMatchOrd (MatchEqv _)     =  2
subMatchOrd MatchAnte        =  3
subMatchOrd MatchCnsq        =  3
subMatchOrd (MatchEqvVar _)  =  3
\end{code}
