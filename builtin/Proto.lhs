\section{Prototype}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proto (
  protoName
, protoTheory
) where

import Data.Maybe
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import Types
import AST
import SideCond
import VarData
import Substitution
import Laws
import Proofs
import Theories

import StdTypeSignature
import StdSignature
import TestRendering
\end{code}

\subsection{Introduction}

This is an isolated theory for prototyping stuff

Right now we use conjectures to provide terms for testing save/load.


Some useful local definitions:
\begin{code}
v_equiv = Vbl equiv ObsV Static
vP = Vbl (jId "P") PredV Static
gvP = StdVar vP
p = jVar pred1 $ vP
q = jVar pred1 $ Vbl (jId "Q") PredV Static
r = jVar pred1 $ Vbl (jId "R") PredV Static
vx = Vbl (jId "x") ObsV Static  ; lvxs = LVbl vx [] []
xs = LstVar lvxs
ve = Vbl (jId "e") ExprV Static ; lves = LVbl ve [] []
sub p   = Sub pred1 p $ jSubstn [] [(lvxs,lves)]
subid p = Sub pred1 p $ xSubstn [] [(lvxs,lvxs)]
\end{code}

\subsubsection{Known Variables}

We have none.
The value $true$ is defined as a value, and not a known variable.
\begin{code}
protoKnown :: VarTable
protoKnown =  newNamedVarTable protoName
\end{code}

\newpage

\subsubsection{Axioms}


We now collect all of the above as our axiom set:
\begin{code}
protoAxioms :: [Law]
protoAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ 
      ]
\end{code}

\subsection{Conjectures}

\begin{code}
tmConj name term = ( name, ( term, scTrue ))

tmTrue = tmConj "true" (Val arbpred (Boolean True))
tmFalse = tmConj "false" (Val arbpred (Boolean False))
tmNumPos = tmConj "fortytwo" (Val arbpred (Integer 42))
tmNumNeg = tmConj "neg99" (Val arbpred (Integer (-99)))
tmVarOS = tmConj ("obs" -.- "static") (jVar arbpred $ Vbl (jId "os") ObsV Static)
\end{code}



Collected\dots
\begin{code}
protoConjs :: [NmdAssertion]
protoConjs = map mkNmdAsn 
  [ tmTrue, tmFalse
  , tmNumPos, tmNumNeg 
  , tmVarOS
  ]
\end{code}

\subsection{The Prototype Theory}

\begin{code}
protoName :: String
protoName = "Proto"
protoTheory :: Theory
protoTheory
  =  nullTheory { thName  =  protoName
                , known   =  protoKnown
                , laws    =  protoAxioms
                , conjs   =  protoConjs
                }
\end{code}
