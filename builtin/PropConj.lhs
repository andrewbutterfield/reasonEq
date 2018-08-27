\section{Propositional Theorems (Conjunction)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropConj (
  propConjName
, propConjTheory
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

import PropAxioms
import PropEquiv
import PropNot
import PropDisj
\end{code}

\subsection{Conjunction Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Conjunction} section.

$$
\CONJPROPCONJ
$$

The absorption rules are in a seperate theory.

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}

\newpage

$$
  \begin{array}{ll}
       \CJandSymm  & \CJandSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandSym
 = ( _land++"_symm"
   , ( (p /\ q) === (q /\ p)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandAssoc & \CJandAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandAssoc
 = ( _land++"_assoc"
   , ( (p /\ q) /\ r === p /\ (q /\ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandIdem & \CJandIdemN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandIdem
 = ( _land++"_idem"
   , ( p /\ p === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandUnit & \CJandUnitN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandUnit
 = ( _land++"_unit"
   , ( p /\ trueP === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandZero & \CJandZeroN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandZero
 = ( _land++"_zero"
   , ( p /\ falseP === falseP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandDistr & \CJandDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandDistr
 = ( _land++"_"++_land++"_distr"
   ,  ( p /\ (q /\ r)  === (p /\ q) /\ (p /\ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJcontradict & \CJcontradictN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjContradict
 = ( _land++"_symm"
   , ( p /\ mkNot p === falseP
     , scTrue ) )
\end{code}

\newpage
Pulling it all together:
\begin{code}
propConjConjs :: [NmdAssertion]
propConjConjs
  = [ cjandSym, cjandAssoc, cjandIdem
    , cjandUnit, cjandZero
    , cjandDistr
    , cjContradict
    ]
\end{code}

\subsection{The Conjunction Theory}

\begin{code}
propConjName :: String
propConjName = "PropConj"
propConjTheory :: Theory
propConjTheory
  =  Theory { thName  =  propConjName
            , thDeps  =  [ propDisjName, propNotName
                         , propEquivName, propAxiomName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propConjConjs
            }
\end{code}
