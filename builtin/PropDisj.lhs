\section{Propositional Theorems (Disjunction)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropDisj (
  propDisjName
, propDisjTheory
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
import Negation
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\lor$,
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


\subsection{Disjunction Axioms}

\subsection{TO BE SHIPPED OUT}


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

\begin{code}
shipAxioms :: [Law]
shipAxioms
  = map labelAsAxiom
      [ axOrSymm, axOrAssoc, axOrIdem, axOrEqvDistr, axExclMidl
      , axGoldRule
      , axImplDef ]
\end{code}

\textbf{END OF STUFF FOR SHIPPING}
\subsection{Disjunction Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Implication} section.

$$
\CONJPROPIMPL
$$


$$
  \begin{array}{ll}
       \CJorZero  & \CJorZeroN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrZero
 = ( "lor"-.-"zero"
   , ( (p \/ trueP) === trueP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJorUnit & \CJorUnitN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrUnit
 = ( "lor"-.-"unit"
   , ( (p \/ falseP) === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJorDistr & \CJorDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrOrDistr
 = ( "lor"-.-"lor"-.-"distr"
   , ( p \/ (q \/ r) === (p \/ q) \/ (p \/ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJorEqvSplit & \CJorEqvSplitN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrEqvSplit
 = ( "lor"-.-"equiv"-.-"split"
   , ( flattenEquiv ( (p \/ q === p \/ mkNot q) === p )
     , scTrue ) )
\end{code}





\begin{code}
propDisjConjs :: [NmdAssertion]
propDisjConjs
  = [ cjOrZero, cjOrUnit, cjOrOrDistr, cjOrEqvSplit
    ]
\end{code}

\subsection{The Disjunction Theory}

\begin{code}
propDisjName :: String
propDisjName = "PropDisj"
propDisjTheory :: Theory
propDisjTheory
  =  Theory { thName  =  propDisjName
            , thDeps  =  [ negationName, equivName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propDisjConjs
            }
\end{code}
