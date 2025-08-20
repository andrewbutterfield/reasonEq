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

-- Values

tmTrue = tmConj "true" (Val arbpred (Boolean True))
tmFalse = tmConj "false" (Val arbpred (Boolean False))

tmNumPos = tmConj "fortytwo" (Val arbpred (Integer 42))
tmNumNeg = tmConj "neg99" (Val arbpred (Integer (-99)))

-- Variables 

mkV nm vc vw = jVar arbpred $ Vbl (jId nm) vc vw

tmVarOS = tmConj ("obs"-.-"static") (mkV "Vo" ObsV Static)
tmVar'OS = tmConj ("obs"-.-"before") (mkV "Vo" ObsV Before)
tmVarOS' = tmConj ("obs"-.-"after") (mkV "Vo" ObsV After)
tmVarOS'd = tmConj ("obs"-.-"during") (mkV "Vo" ObsV (During "d"))

tmVarES = tmConj ("expr"-.-"static") (mkV "Ve" ExprV Static)
tmVar'ES = tmConj ("expr"-.-"before") (mkV "Ve" ExprV Before)
tmVarES' = tmConj ("expr"-.-"after") (mkV "Ve" ExprV After)
tmVarES'd = tmConj ("expr"-.-"during") (mkV "Ve" ExprV (During "d"))

tmVarPS = tmConj ("pred"-.-"static") (mkV "Vp" PredV Static)
tmVar'PS = tmConj ("pred"-.-"before") (mkV "Vp" PredV Before)
tmVarPS' = tmConj ("pred"-.-"after") (mkV "Vp" PredV After)
tmVarPS'd = tmConj ("pred"-.-"during") (mkV "Vp" PredV (During "d"))

-- Constructions

cs = True ; ns = False -- Subable
vT = mkV "T" PredV Static
mkCons nm subable ts = Cons arbpred subable (jId nm) ts



tmConsS0 = tmConj ("cons"-.-"S"-.-"zero") (mkCons "cs0" cs [])
tmConsS1 = tmConj ("cons"-.-"S"-.-"one")  (mkCons "cs1" cs [vT])
tmConsS2 = tmConj ("cons"-.-"S"-.-"two")  (mkCons "cs2" cs [vT,vT])

tmConsN0 = tmConj ("cons"-.-"N"-.-"zero") (mkCons "ns0" ns [])
tmConsN1 = tmConj ("cons"-.-"N"-.-"one")  (mkCons "ns1" ns [vT])
tmConsN2 = tmConj ("cons"-.-"N"-.-"two")  (mkCons "ns2" ns [vT,vT])

tmConsNest = tmConj ("cons"-.-"nesting")
              (mkCons "nest" cs [ mkCons "sub1" cs []
                                , mkCons "sub2" cs [vT] 
                                , mkCons "sub3" cs [] 
                                ])

\end{code}



Collected\dots
\begin{code}
protoConjs :: [NmdAssertion]
protoConjs = map mkNmdAsn 
  [ tmTrue, tmFalse
  , tmNumPos, tmNumNeg 
  , tmVarES, tmVar'ES, tmVarES', tmVarES'd
  , tmVarPS, tmVar'PS, tmVarPS', tmVarPS'd
  , tmConsS0, tmConsS1, tmConsS2
  , tmConsN0, tmConsN2, tmConsN2, tmConsNest
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
