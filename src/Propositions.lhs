\section{Propositional Calculus}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Propositions (
  bool
, true, trueP
, false, falseP
, equiv, mkEquiv, mkEquivs
, lnot, mkNot
, lor, mkOr, mkOrs
, land, mkAnd, mkAnds
, implies, mkImplies
, propKnown
, propLaws
) where

import Data.Maybe

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData

-- import Test.HUnit
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)
\end{code}


\subsection{Introduction}

Here we present a hard-coded implementation of
propositional equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
$$
\AXPROP
$$

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
the $\Bool$ type,
the constants \textit{true} and \textit{false},
and the infix symbols $\equiv$, $lnot$, $\lor$, $\land$ and $\implies$.
The propositional constants, along with the equivelance and implication operators
are also exported as they have significance for proof strategies.

\subsection{Predicate Variables}

\begin{code}
p = Vbl (fromJust $ ident "P") PredV Static
q = Vbl (fromJust $ ident "Q") PredV Static
r = Vbl (fromJust $ ident "R") PredV Static
\end{code}

\subsubsection{Propositional Type}

\begin{code}
bool = GivenType $ fromJust $ ident $ _mathbb "B"
\end{code}

\subsection{Propositional Constants}

\begin{code}
true = Vbl (fromJust $ ident "true") PredV Static
trueP = fromJust $ pVar true
false = Vbl (fromJust $ ident "false") PredV Static
falseP = fromJust $ pVar false
\end{code}

\subsection{Known Variables}

These are precisely the two propositional constants.
\begin{code}
propKnown :: VarTable
propKnown
 = fromJust $ addKnownVar true  bool $
   fromJust $ addKnownVar false bool newVarTable
\end{code}

\subsection{Propositional Operators}

\begin{code}
equiv = fromJust $ ident _equiv ; mkEquivs ps = PCons equiv ps
mkEquiv p q = mkEquivs [p,q]

lnot = fromJust $ ident _lnot ; mkNot p = PCons lnot [p]

lor = fromJust $ ident _lor
mkOrs []   =  falseP
mkOrs [p]  =  p
mkOrs ps   =  PCons lor ps
mkOr p q   =  mkOrs [p,q]

land = fromJust $ ident _land
mkAnds []   =  trueP
mkAnds [p]  =  p
mkAnds ps   =  PCons land ps
mkAnd p q = mkAnds [p,q]

implies = fromJust $ ident _implies ; mkImplies p q = PCons implies [p,q]
\end{code}

\subsection{Propositional Axioms}
$$
  \begin{array}{ll}
     \AXeqvAssoc & \AXeqvAssocN
  \\ \AXeqvSymm & \AXeqvSymmN
  \\ \AXeqvId & \AXeqvIdN
  \\ \AXfalseDef &\AXfalseDefN
  \\ \AXnotEqvDistr & \AXnotEqvDistrN
  \\ \AXorSymm & \AXorSymmN
  \\ \AXorAssoc & \AXorAssocN
  \\ \AXorIdem & \AXorIdemN
  \\ \AXorEqvDistr & \AXorEqvDistrN
  \\ \AXexclMdl & \AXexclMdlN
  \\ \AXgoldRule & \AXgoldRuleN
  \\ \AXimplDef & \AXimplDefN
  \end{array}
$$

\begin{code}

propLaws :: [(Term,SideCond)]
propLaws = []

\end{code}
