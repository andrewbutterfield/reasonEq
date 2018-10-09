\section{Theory of Equality}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Equality (
  equals, isEqualTo
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
import PropAxioms
\end{code}


\newpage
\subsection{Introduction}

Here we present a hard-coded implementation
a very simple theory of equality.
$$
\AXEQUALITY
$$

We need to build some infrastructure here.
This consists of the expression variables $e$, $f$ and $g$,
and the constant $=$.

\subsection{Predicate Variables}

\begin{code}
e = fromJust $ eVar ArbType $ Vbl (fromJust $ ident "e") ExprV Static
f = fromJust $ eVar ArbType $ Vbl (fromJust $ ident "f") ExprV Static
g = fromJust $ eVar ArbType $ Vbl (fromJust $ ident "g") ExprV Static
\end{code}

\subsection{Predicate Constants}

\begin{code}
equals = fromJust $ ident "="
isEqualTo e1 e2 = Cons P equals [e1,e2]
\end{code}


\subsection{Predicate Axioms}

\subsubsection{Axioms}

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
  =  Theory { thName  =  equalityName
            , thDeps  =  [ ]
            , known   =  newVarTable
            , laws    =  equalityAxioms
            , proofs  =  []
            , conjs   =  []
            }
\end{code}
