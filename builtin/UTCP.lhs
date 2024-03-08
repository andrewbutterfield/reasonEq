\chapter{Unifying Theories of Concurrent Programming}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTCP (
  utcpConjs, utcpName, utcpTheory
) where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Substitution
import Theories

import StdTypeSignature
import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import Implication
import Equality
import ForAll
import Exists
import UClose
import UTPSignature
import UTPBase
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we implement the rooted version of UTCP.



\newpage
\section{UTCP Theory}

We collect our known variables:
\begin{code}
utcpKnown
 = newVarTable
\end{code}


We now collect our axiom set:
\begin{code}
utcpAxioms :: [Law]
utcpAxioms
  = map labelAsAxiom
      [ 
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utcpConjs :: [NmdAssertion]
utcpConjs
  = [ 
    ]
\end{code}



\begin{code}
utcpName :: String
utcpName = "UTCP"
utcpTheory :: Theory
utcpTheory
  =  nullTheory { thName  =  utcpName
            , thDeps  =  [ utpBaseName
                         , uCloseName
                         , existsName
                         , forallName
                         , equalityName
                         , implName
                         , aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , known   =  utcpKnown
            , laws    =  utcpAxioms
            , conjs   =  utcpConjs
            }
\end{code}
