\section{Propositional Theorems (Equivalence)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropEquiv (
  propEquivName
, propEquivTheory
) where

import Data.Maybe

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Theories

import PropAxioms
import TestRendering
\end{code}

\subsection{Equivalence Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Equivalence and True} section.

Here there is only one, which in \cite{gries.93} is considered an axiom:
$$
  \begin{array}{ll}
     \CJeqvId & \CJeqvIdN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjEqvId
 = ( "equiv"-.-"id"
   , ( (trueP === q) === q
     , scTrue ) )

q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static

propEquivConjs :: [NmdAssertion]
propEquivConjs = [ cjEqvId ]
\end{code}

\subsection{The Equivalence Theory}

\begin{code}
propEquivName :: String
propEquivName = "PropEquiv"
propEquivTheory :: Theory
propEquivTheory
  =  Theory { thName  =  propEquivName
            , thDeps  =  [propAxiomName]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propEquivConjs
            }
\end{code}
