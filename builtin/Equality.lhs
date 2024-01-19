\chapter{Theory of Equality}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Equality (
  equalityAxioms, equalityName, equalityTheory
) where

import Data.Maybe
import qualified Data.Map as M

import LexBase
import Variables
import AST
import SideCond
import VarData
import Substitution
import Laws
import Proofs
import Theories
import StdTypeSignature
import StdSignature
import Equivalence
import Implication
import TestRendering
\end{code}

\section{Introduction}

Here we present a hard-coded implementation
a very simple theory of equality.
$$
\AXEQUALITY
$$

We need to build some infrastructure here.
This consists of the expression variables $e$, $f$ and $g$,
the constant $=$,
and expression list-variables $\lst e,\lst f$.

\section{Equality Variables}

\begin{code}
v_eq = Vbl equals PredV Static
ve = Vbl (jId "e") ExprV Static; lves = LVbl ve [] []
e = fromJust $ eVar ArbType ve
es = LVbl ve [] []
vf = Vbl (jId "f") ExprV Static
f = fromJust $ eVar ArbType vf
fs = LVbl vf [] []
vg = Vbl (jId "g") ExprV Static
g = fromJust $ eVar ArbType vg
vx = Vbl (jId "x") ObsV Static  ; lvxs = LVbl vx [] []
\end{code}

\section{Equality Constants}

\begin{code}
sub e = Sub ArbType e $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\section{Equality Known Variables}

\begin{code}
eqKnown :: VarTable
eqKnown =  fromJust $ addKnownVar v_eq boolf_2 $ newVarTable
\end{code}



\section{Equality Axioms}

$$\begin{array}{ll}
   \AXequalRefl & \AXequalReflN
\end{array}$$

\vspace{-8pt}
\begin{code}
axEqualRefl
 = ( "=" -.- "refl"
   , ( e `isEqualTo` e
   , scTrue ) )
\end{code}

$$\begin{array}{ll}
   \AXequalSymm & \AXequalSymmN
\end{array}$$

\vspace{-8pt}
\begin{code}
axEqualSymm
 = ( "=" -.- "symm"
   , ( (e `isEqualTo` f) === (f `isEqualTo` e)
   , scTrue ) )
\end{code}

$$\begin{array}{ll}
   \AXequalTrans & \AXequalTransN
\end{array}$$

\vspace{-8pt}
\begin{code}
axEqualTrans
 = ( "=" -.- "trans"
   , ( ( e `isEqualTo` f) /\ ( f `isEqualTo` g) ==> (e `isEqualTo` g)
   , scTrue ) )
\end{code}

$$\begin{array}{ll}
     \AXequalsSplit & \AXequalsSplitN
\end{array}$$
This axiom is encoded by the fact that \texttt{Iter}
specifies both relational and joining predicates,
which \texttt{areEqualTo} defines as $=$ and $\land$ respectively.

We collect these together:
\begin{code}
equalityAxioms :: [Law]
equalityAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ axEqualRefl, axEqualSymm, axEqualTrans ]
\end{code}

\section{Equality Conjectures}

$$\begin{array}{ll}
   \AXequalSubst & \AXequalSubstN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjEqualSubst
 = ( "=" -.- "subst"
   , ( sub ( e `isEqualTo` f) === ((sub e) `isEqualTo` (sub f))
   , scTrue ) )
\end{code}


Collecting \dots
\begin{code}
equalityConjectures :: [NmdAssertion]
equalityConjectures
  = map mkNmdAsn [ cjEqualSubst ]
\end{code}

\section{The Equality Theory}

\begin{code}
equalityName :: String
equalityName = "Equality"
equalityTheory :: Theory
equalityTheory
  =  nullTheory { thName  =  equalityName
                , thDeps  =  [ implName
                             , equivName ]
                , known   =  eqKnown
                , laws    =  equalityAxioms
                , conjs   =  equalityConjectures
                }
\end{code}
