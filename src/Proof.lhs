\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proof
 ( Assertion
 , Justification
 , CalcStep
 , Calculation
 , LiveProof
 ) where

-- import Data.Set (Set)
-- import qualified Data.Set as S
-- import Data.Maybe
--
-- import Utilities
-- import LexBase
-- import Variables
import AST
import SideCond
import TermZipper
-- import VarData
-- import Binding
-- import Matching
-- import Builder
--
-- import NiceSymbols
-- import TestRendering
--
-- import Test.HUnit hiding (Assertion)
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for the key concepts behind a proof,
such as the notion of assertions, proof strategies,
and proof calculations.

\subsection{Assertions}

An assertion is simply a predicate term coupled with side-conditions.
\begin{code}
type Assertion = (Term, SideCond)
\end{code}

\subsection{Proof Calculations}

We start with the simplest proof process of all,
namely a straight calculation from a starting assertion
to a specified final assertion, usually being the axiom \textit{true}.
We need to have an AST zipper to allow sub-terms to be singled out
for match and replace,
and some way of recording what happenned,
so that proofs (complete or partial) can be saved,
restored, and reviewed.

The actions involed in a proof calculation step are as follows:
\begin{itemize}
  \item Select sub-term.
  \item Match against laws.
  \item Select preferred match and apply its replacement.
  \item Record step (which subterm, which law).
\end{itemize}

We want a zipper for the first three,
and a calculation-step record for the fourth.
We will prototype something simple for now.
\begin{code}
type Justification
  = ( String   -- law name
    , [Int] )  -- zipper descent arguments

type CalcStep
  = ( Justification -- step justification
    , Term )  -- previous term

type Calculation
  = ( Term -- end (or current) term
    , [ CalcStep ] )  -- calculation steps, most recent first

type LiveProof
  = ( TermZip  -- current term, focussed
    , [Int] -- current zipper descent arguments
    , [CalcStep]  -- calculation steps so far.
    )
\end{code}
