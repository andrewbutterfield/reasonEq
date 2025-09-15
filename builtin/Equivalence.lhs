\section{Propositional Theorems (Equivalence)}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018

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

import Symbols

import Utilities
import LexBase
import Variables
import Types
import AST
import SideCond
import VarData
import Substitution
import Laws
import Proofs
import Theories

import StdTypeSignature
import StdSignature
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\equiv$ and $true$,
based on \cite{gries.93},
along with two substitution axioms.

$$
\AXEQUIV
$$

Some useful local definitions:
\begin{code}
v_equiv = Vbl equiv ObsV Static
vP = Vbl (jId "P") PredV Static
gvP = StdVar vP
p = jVar pred1 $ vP
q = jVar pred1 $ Vbl (jId "Q") PredV Static
r = jVar pred1 $ Vbl (jId "R") PredV Static
vx = Vbl (jId "x") ObsV Static  ; lvxs = LVbl vx [] []
xs = LstVar lvxs
ve = Vbl (jId "e") ExprV Static ; lves = LVbl ve [] []
sub p   = Sub pred1 p $ jSubstn [] [(lvxs,lves)]
subid p = Sub pred1 p $ xSubstn [] [(lvxs,lvxs)]
\end{code}

\subsubsection{Known Variables}

We have none.
The value $true$ is defined as a value, and not a known variable.
\begin{code}
equivKnown :: VarTable
equivKnown =  fromJust $ addKnownConstructor v_equiv boolf_2 True
                       $ newNamedVarTable equivName
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
 = ( "eqv" -.- "refl"
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
 = ( "eqv" -.- "assoc"
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
 = ( "eqv" -.- "symm"
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

$$
\begin{array}{ll}
   \AXnonSubst, \AXnonSubstS & \AXnonSubstN
\end{array}  
$$
\begin{code}
axNonSubst
 = ( "non" -.- "subst"
   , ( sub p === p
     , [xs] `notin` gvP ) )
\end{code}

We now collect all of the above as our axiom set:
\begin{code}
equivAxioms :: [Law]
equivAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ axTrue
      , axEqvRefl, axEqvAssoc, axEqvSymm
      , axIdSubst, axNonSubst
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
 = ( "eqv"-.-"id"
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
 = ( "eqv"-.-"subst"
   , ( sub (p === q) === ((sub p) === (sub q))
     , scTrue ) )
\end{code}

Collected\dots
\begin{code}
equivConjs :: [NmdAssertion]
equivConjs = map mkNmdAsn [ cjEqvId, cjTrueSubst, cjEqvSubst ]
\end{code}

\subsection{The Equivalence Theory}

\begin{code}
equivName :: String
equivName = "EQV"
equivTheory :: Theory
equivTheory
  =  nullTheory { thName  =  equivName
                , known   =  equivKnown
                , laws    =  equivAxioms
                , conjs   =  equivConjs
                }
\end{code}
