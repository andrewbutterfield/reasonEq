\section{Propositional Theorems (Mixed Operators I)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropMixOne (
  propMixOneName
, propMixOneTheory
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
\end{code}

\subsection{MixOne Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the second part of the \textsc{Conjunction} section,
which deals with laws involving a mix of conjunctions and other
previously defined operators.

$$
\CONJPROPMIXONE
$$

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}


$$
  \begin{array}{ll}
     \CJeqvId & \CJeqvIdN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjEqvId
 = ( _equiv++"_id"
   , ( (trueP === q) === q
     , scTrue ) )
\end{code}




\begin{code}
propMixOneConjs :: [NmdAssertion]
propMixOneConjs
  = [ --
    ]
\end{code}

\subsection{The MixOne Theory}

\begin{code}
propMixOneName :: String
propMixOneName = "PropMixOne"
propMixOneTheory :: Theory
propMixOneTheory
  =  Theory { thName  =  propMixOneName
            , thDeps  =  [ propConjName, propDisjName, propNotName
                         , propEquivName, propAxiomName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propMixOneConjs
            }
\end{code}
