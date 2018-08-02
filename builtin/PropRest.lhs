\section{Propositional Theorems (THE-REST)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropRest (
  propXxxName
, propXxxTheory
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

import Propositions
import PropXxx
\end{code}

\subsection{Xxx Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Xxx} section.

$$
\CONJPROP
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



$$
  \begin{array}{ll}
     \CJorZero & \CJorZeroN
  \end{array}
$$
\begin{code}
cjOrZero
 = ( _lor++"_zero"
   , ( p \/ trueP === trueP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJweakenImp & \CJweakenImpN
  \end{array}
$$
\begin{code}
cjWeakImp
 = ( "weaken_"++_implies
   , ( p /\ q ==> p
     , scTrue ) )
\end{code}


\begin{code}
propXxxConjs :: [NmdAssertion]
propXxxConjs
  = [ cjEqvId, cjOrZero, cjWeakImp
    ]
\end{code}

\subsection{The Xxx Theory}

\begin{code}
propXxxName :: String
propXxxName = "PropXxx"
propXxxTheory :: Theory
propXxxTheory
  =  Theory { thName  =  propXxxName
            , thDeps  =  [propAxiomName]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propXxxConjs
            }
\end{code}
