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
import PropEquiv
import PropNot
import TestRendering
\end{code}

\subsection{Implication Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Implication} section.

$$
\CONJPROPIMPL
$$

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}


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
            , thDeps  =  [ propNotName, propEquivName, propAxiomName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propDisjConjs
            }
\end{code}
