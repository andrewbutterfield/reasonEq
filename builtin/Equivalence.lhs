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
import qualified Data.Map as M

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Substitution
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
vx = Vbl (fromJust $ ident "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (fromJust $ ident "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsubsection{Known Variables}

We have none.
The value $true$ is defined as a value, and not a known variable.
\begin{code}
equivKnown :: VarTable
equivKnown =  newVarTable
\end{code}

\subsubsection{Substitutability}

$$
  \begin{array}{ll}
     \AXeqvSubst & \AXeqvSubstN
  \\ \AXtrueSubst & \AXtrueSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
equivSubAble = M.fromList [(equiv,CS)]
-- true is a value, and so is automatically NS
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



We now collect all of the above as our axiom set:
\begin{code}
equivAxioms :: [Law]
equivAxioms
  = map labelAsAxiom
      [ axTrue
      , axEqvRefl, axEqvAssoc, axEqvSymm
      ]
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
            , subable =  equivSubAble
            , laws    =  equivAxioms
            , proofs  =  []
            , conjs   =  equivConjs
            }
\end{code}
