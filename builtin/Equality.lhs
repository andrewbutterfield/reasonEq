\section{Theory of Equality}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Equality (
  equals, isEqualTo, areEqualTo
, equalityAxioms, equalityName, equalityTheory
) where

import Data.Maybe

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

Here we present a hard-coded implementation
a very simple theory of equality.
$$
\AXEQUALITY
$$

We need to build some infrastructure here.
This consists of the expression variables $e$, $f$ and $g$,
the constant $=$,
and expression list-variables $\lst e,\lst f$.

\subsection{Equality Variables}

\begin{code}
ve = Vbl (fromJust $ ident "e") ExprV Static
e = fromJust $ eVar ArbType ve
es = LVbl ve [] []
vf = Vbl (fromJust $ ident "f") ExprV Static
f = fromJust $ eVar ArbType vf
fs = LVbl vf [] []
vg = Vbl (fromJust $ ident "g") ExprV Static
g = fromJust $ eVar ArbType vg
\end{code}

\subsection{Equality Constants}

\begin{code}
equals = fromJust $ ident "="
isEqualTo e1 e2 = Cons P equals [e1,e2]
areEqualTo es1 es2 = Iter P land equals [es1,es2]
\end{code}


\newpage
\subsection{Equality Axioms}

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
  = map labelAsAxiom
      [ axEqualRefl, axEqualSymm, axEqualTrans ]
\end{code}


\subsection{The Equality Theory}

\begin{code}
equalityName :: String
equalityName = "Equality"
equalityTheory :: Theory
equalityTheory
  =  nullTheory { thName  =  equalityName
            , laws    =  equalityAxioms
            }
\end{code}
