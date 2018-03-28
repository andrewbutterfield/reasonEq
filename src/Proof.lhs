\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proof
 ( Assertion
 ) where

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Binding
import Matching
import Builder

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
