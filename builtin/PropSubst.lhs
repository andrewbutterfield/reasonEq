\section{Propositional Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropSubst (
  propSubstName
, propSubstTheory
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
import Disjunction
import Conjunction
import PropImpl
import TestRendering
\end{code}


\newpage
\subsection{Introduction}


Here we have axioms that state that substitutions
distribute through certain propositional operators.

$$
\AXPROPSUBST
$$

The rest are provable as conjectures:

$$
\CJPROPSUBST
$$

\subsection{Propositional Variables and substitution}

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static

vx = Vbl (fromJust $ ident "x") ObsV Static
lvxs = LVbl vx [] []

ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] []

sub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}


\subsubsection{Propositional Substitution Conjectures}






\begin{code}
propSubstConjs :: [NmdAssertion]
propSubstConjs  =  [  ]
\end{code}


\subsection{The Propositional Theory}

\begin{code}
propSubstName :: String
propSubstName = "PropSubst"
propSubstTheory :: Theory
propSubstTheory
  =  Theory { thName  =  propSubstName
            , thDeps  =  [ propImplName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propSubstConjs
            }
\end{code}
