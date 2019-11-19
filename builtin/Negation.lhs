\section{Propositional Theorems (Negation)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Negation (
  notName
, notTheory
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
import Equivalence
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\lnot$ and $false$,
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
The value $false$ is defined as a value, and not a known variable.
\begin{code}
negationKnown :: VarTable
negationKnown =  newVarTable
\end{code}

\newpage
\subsection{Negation Axioms}

$$
  \begin{array}{ll}
     \AXfalseDef & \AXfalseDefN
  \end{array}
$$

\begin{code}
axFalseDef  =  ( "false"-.-"def", ( falseP === mkNot trueP, scTrue ) )
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
     \AXnotSubst & \AXnotSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axNotSubst
 = ( "lnot" -.- "subst"
   , ( sub (mkNot p)  === mkNot (sub p)
   , scTrue ) )
\end{code}






\begin{code}
negationAxioms :: [Law]
negationAxioms  = map labelAsAxiom [ axFalseDef, axNotEqvDistr, axNotSubst ]
\end{code}

\subsection{Negation Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Negation, Inequivalence and FALSE} section,
except those about inequivalence.

$$
\CONJPROPNOT
$$


$$
  \begin{array}{ll}
     \CJfalseSubst & \CJfalseSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjFalseSubst
 = ( "false" -.- "subst"
   , ( sub falseP  === falseP
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
       \CJswapNot  & \CJswapNotN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjSwapNot
 = ( "lnot"-.-"equiv"-.-"swap"
   , (  (mkNot p === q) === (p === mkNot q)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJnotInvol & \CJnotInvolN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjNotInvol
 = ( "lnot"-.-"invol"
   , ( mkNot (mkNot p) === p
     , scTrue ) )
\end{code}

\newpage
$$
  \begin{array}{ll}
       \CJnotFalse & \CJnotFalseN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjNotFalse
 = ( "false_neg"
   , ( mkNot falseP === trueP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJnotDef   & \CJnotDefN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjNotDef
 = ( "lnot"-.-"def"
   , ( mkNot p === (p === falseP)
     , scTrue ) )
\end{code}




\begin{code}
negationConjs :: [NmdAssertion]
negationConjs
  = [ cjFalseSubst, cjSwapNot, cjNotInvol, cjNotFalse, cjNotDef
    ]
\end{code}

\subsection{The Negation Theory}

\begin{code}
notName :: String
notName = "Not"
notTheory :: Theory
notTheory
  =  Theory { thName  =  notName
            , thDeps  =  [equivName]
            , known   =  newVarTable
            , laws    =  negationAxioms
            , proofs  =  []
            , conjs   =  negationConjs
            }
\end{code}