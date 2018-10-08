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
 = propdef ( _implies++"_def2"
           , (p ==> q) === (mkNot p \/ q) )
\end{code}


$$\begin{array}{ll}
  \CJImpMeet & \CJImpMeetN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpMeet
 = propdef ( _implies++"_meet"
           , (p ==> q) === (p /\ q === p) )
\end{code}


$$\begin{array}{ll}
  \CJContraPos & \CJContraPosN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjContra
 = propdef ( "contrapostive"
           , (p ==> q) === (mkNot q ==> mkNot p) )
\end{code}


$$\begin{array}{ll}
  \CJImpEqvDistr & \CJImpEqvDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpEqvDistr
 = propdef ( _implies++"_"++_equiv++"_distr"
           , (p ==> (q === r)) === ((p ==> q) === (p ==> r)) )
\end{code}

$$\begin{array}{ll}
  \CJShunting & \CJShuntingN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjShunting
 = propdef ( "shunting"
           , (p /\ q ==> r) === (p ==> (q ==> r)) )
\end{code}


$$\begin{array}{ll}
  \CJAndImp & \CJAndImpN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAndImp
 = propdef ( "GS3.66"
           , (p /\ (p ==> q)) === (p /\ q) )
\end{code}


$$\begin{array}{ll}
  law & name
\end{array}$$

\vspace{-8pt}
\begin{code}
cjXXX
 = propdef ( "XXX"
           , p /\ q \/ r /\ s )
\end{code}



Pulling them all together:
\begin{code}
propImplConjs :: [NmdAssertion]
propImplConjs
  = [ cjImpDef2, cjImpMeet, cjContra, cjImpEqvDistr, cjShunting
    , cjAndImp
    ]
\end{code}


\newpage
to be done \dots
$$
\begin{array}{ll}
     \CJAndPmi & \CJAndPmiN
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
