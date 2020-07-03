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
based on \cite{gries.93},
along with one key axiom regarding identity substitutions.

$$
\AXEQUIV
$$

Some useful local definitions:
\begin{code}
v_equiv = Vbl equiv PredV Static
p = jVar P $ Vbl (jId "P") PredV Static
q = jVar P $ Vbl (jId "Q") PredV Static
r = jVar P $ Vbl (jId "R") PredV Static
vx = Vbl (jId "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (jId "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
subid p = Sub P p $ fromJust $ substn [] [(lvxs,lvxs)]
\end{code}

\subsubsection{Known Variables}

We have none.
The value $true$ is defined as a value, and not a known variable.
\begin{code}
equivKnown :: VarTable
equivKnown =  fromJust $ addKnownVar v_equiv boolf_2 $ newVarTable
\end{code}

\newpage
\subsubsection{Substitutability}

$$
  \begin{array}{ll}
     \AXeqvSubst & \AXeqvSubstN
  \\ \AXtrueSubst & \AXtrueSubstN
  \end{array}
$$

%\vspace{-8pt}
\begin{code}
equivSubAble = M.fromList [(equiv,CS)]
-- true is a value, and so is automatically NS
\end{code}


\subsubsection{Axioms}

We take \textit{true} to be axiomatic,
rather than a theorem, for reasons of efficiency.
$$
  \begin{array}{ll}
     \AXtrue     & \AXtrueN
  \end{array}
$$

\begin{code}
axTrue  =  ( "true", ( trueP, scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXeqvRefl & \AXeqvReflN
  \end{array}
$$

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

\begin{code}
axEqvSymm
 = ( "equiv" -.- "symm"
   , ( flattenEquiv ( (p === q) === (q === p) )
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \AXidSubst & \AXidSubstN
  \end{array}
$$
\begin{code}
axIdSubst
 = ( "id" -.- "subst"
   , ( subid p === p
     , scTrue ) )
\end{code}

We now collect all of the above as our axiom set:
\begin{code}
equivAxioms :: [Law]
equivAxioms
  = map labelAsAxiom
      [ axTrue
      , axEqvRefl, axEqvAssoc, axEqvSymm
      , axIdSubst
      ]
\end{code}

\subsection{Equivalence Conjectures}

Apart from the substituability conectures,
there is only one other conjecture
that, in \cite{gries.93}, is considered an axiom:
$$
  \begin{array}{ll}
     \CJeqvId & \CJeqvIdN
  \end{array}
$$
\begin{code}
cjEqvId
 = ( "equiv"-.-"id"
   , ( (trueP === q) === q
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXtrueSubst & \AXtrueSubstN
  \end{array}
$$
\begin{code}
cjTrueSubst
 = ( "true"-.-"subst"
   , ( sub trueP === trueP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXeqvSubst & \AXeqvSubstN
  \end{array}
$$
\begin{code}
cjEqvSubst
 = ( "equiv"-.-"subst"
   , ( sub (p === q) === ((sub p) === (sub q))
     , scTrue ) )
\end{code}

Collected\dots
\begin{code}
equivConjs :: [NmdAssertion]
equivConjs = [ cjEqvId, cjTrueSubst, cjEqvSubst ]
\end{code}

\subsection{The Equivalence Theory}

\begin{code}
equivName :: String
equivName = "Equiv"
equivTheory :: Theory
equivTheory
  =  nullTheory { thName  =  equivName
                , known   =  equivKnown
                , subable =  equivSubAble
                , laws    =  equivAxioms
                , conjs   =  equivConjs
                }
\end{code}
