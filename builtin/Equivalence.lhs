\section{Propositional Theorems (Equivalence)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Equivalence (
  equivName
, equivTheory
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

import StdSignature
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\equiv$ and $true$,
based on \cite{gries.93}.

Some useful local definitions:
\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}

\subsubsection{Known Variables}

We have none.
The values $true$ and $false$ are defined as values,
not known variables.
\begin{code}
equivKnown :: VarTable
equivKnown =  newVarTable
\end{code}


\newpage
\subsubsection{Axioms}

We take \textit{true} to be axiomatic,
rather than a theorem, for reasons of efficiency.
$$
  \begin{array}{ll}
     \AXtrue     & \AXtrueN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axTrue  =  ( "true", ( trueP, scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXeqvRefl & \AXeqvReflN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvRefl
 = ( "equiv" -.- "refl"
   , ( p === p
     , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXeqvAssoc & \AXeqvAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvAssoc
 = ( "equiv" -.- "assoc"
   , ( ((p === q) === r) === (p === (q === r))
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXeqvSymm & \AXeqvSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvSymm
 = ( "equiv" -.- "symm"
   , ( flattenEquiv ( (p === q) === (q === p) )
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXnotEqvDistr & \AXnotEqvDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axNotEqvDistr
 = ( "lnot" -.- "equiv" -.- "distr"
   , ( mkNot(p === q) ===  ((mkNot p) === q)
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXorSymm & \AXorSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrSymm
 = ( "lor" -.- "symm"
   , ( p \/ q === q \/ p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorAssoc & \AXorAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrAssoc
 = ( "lor" -.- "assoc"
   , ( (p \/ q) \/ r === p \/ (q \/ r)
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorIdem & \AXorIdemN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrIdem
 = ( "lor" -.- "idem"
   , ( p \/ p === p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorEqvDistr & \AXorEqvDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrEqvDistr
 = ( "lor" -.- "equiv" -.- "distr"
   , ( flattenEquiv ( (p \/ (q === r)) === (p \/ q === p \/ r) )
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXexclMdl & \AXexclMdlN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axExclMidl
 = ( "excl-middle"
   , ( p \/ mkNot p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXgoldRule & \AXgoldRuleN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axGoldRule
 = ( "golden-rule"
   , ( (p /\ q) === ((p === q) === p \/ q)
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXimplDef & \AXimplDefN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axImplDef
 = ( "implies" -.- "def"
   , ( flattenEquiv ( p ==> q === (p \/ q === q) )
   , scTrue ) )
\end{code}

We now collect all of the above as our axiom set:
\begin{code}
equivAxioms :: [Law]
equivAxioms
  = map labelAsAxiom
      [ axTrue, axEqvRefl, axEqvAssoc, axEqvSymm
      , axNotEqvDistr
      , axOrSymm, axOrAssoc, axOrIdem, axOrEqvDistr, axExclMidl
      , axGoldRule, axImplDef ]
\end{code}

\subsection{Equivalence Conjectures}

Here there is only one,
which in \cite{gries.93} is considered an axiom:
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

equivConjs :: [NmdAssertion]
equivConjs = [ cjEqvId ]
\end{code}

\subsection{The Equivalence Theory}

\begin{code}
equivName :: String
equivName = "Equiv"
equivTheory :: Theory
equivTheory
  =  Theory { thName  =  equivName
            , thDeps  =  []
            , known   =  equivKnown
            , laws    =  equivAxioms
            , proofs  =  []
            , conjs   =  equivConjs
            }
\end{code}
