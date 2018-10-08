\section{Propositional Theorems (Implication)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropImpl (
  propImplName
, propImplTheory
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
import PropConj
import PropMixOne
\end{code}

\newpage
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
s = fromJust $ pVar $ Vbl (fromJust $ ident "S") PredV Static
\end{code}


$$\begin{array}{ll}
  \CJImpDefTwo & \CJImpDefTwoN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpDef2
 = ( _implies++"_def2"
   , ( (p ==> q) === (mkNot p \/ q)
     , scTrue ) )
\end{code}


\newpage
to be done \dots
$$
\begin{array}{ll}
     \CJImpMeet & \CJImpMeetN
  \\ \CJContraPos & \CJContraPosN
  \\ \CJImpEqvDistr & \CJImpEqvDistrN
  \\ \CJShunting & \CJShuntingN
  \\ \CJAndImp & \CJAndImpN
  \\ \CJAndPmi & \CJAndPmiN
  \\ \CJOrImp & \CJOrImpN
  \\ \CJOrPmi & \CJOrPmiN
  \\ \CJOrImpAnd & \CJOrImpAndN
  \\ \CJImpRefl & \CJImpReflN
  \\ \CJImpRZero & \CJImpRZeroN
  \\ \CJImpLUnit & \CJImpLUnitN
  \\ \CJNotDefTwo & \CJNotDefTwoN
  \\ \CJFalseImp & \CJFalseImpN
  \\ \CJImpTrans & \CJImpTransN
  \\ \CJEqvImpTrans & \CJEqvImpTransN
  \\ \CJImpEqvTrans & \CJImpEqvTransN
  \\ \CJAnteStrngthn & \CJAnteStrngthnN
  \\ \CJCnsqWkn & \CJCnsqWknN
  \\ \CJAnteOrDistr & \CJAnteOrDistrN
  \\ \CJAnteAndDistr & \CJAnteAndDistrN
  \\ \CJCnsqAndDistr & \CJCnsqAndDistrN
  \\ \CJCnsqOrDistr & \CJCnsqOrDistrN
  \\ \CJAnteAsImpl & \CJAnteAsImplN
\end{array}
$$

\subsection{The Implication Theory}


\begin{code}
propImplConjs :: [NmdAssertion]
propImplConjs
  = [ cjImpDef2
    ]

propImplName :: String
propImplName = "PropImpl"
propImplTheory :: Theory
propImplTheory
  =  Theory { thName  =  propImplName
            , thDeps  =  [ propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propImplConjs
            }
\end{code}
