\section{Propositional Calculus}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Propositions where

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
This consists of the predicates variables $P$, $Q$ and $R$,
the constants \textit{true} and \textit{false},
and the infix symbols $\equiv$, $lnot$, $\lor$, $\land$ and $\implies$.
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
