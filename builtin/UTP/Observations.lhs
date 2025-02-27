\chapter{UTP Observations}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.Observations (
  isUTPDynObs, areUTPDynObs, isUTPCond, areUTPCond, isUTPStcObs
, areUTPStcObs
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
import StdTypeSignature
import UTP.Reading
import UTP.While.RefineSig
import TestRendering

import Debugger
\end{code}


\section{Introduction}

$$ O', O, O_0, [O_0/O'], [O_0/O']$$
\begin{code}
o = jId "O"  ;  vO = PreVar o
lO = PreVars o  ;  lO' = PostVars o  ;  lO0 = MidVars o "0"
gO = LstVar lO  ;  gO' = LstVar lO'  ;  gO0 = LstVar lO0
o0'sub = jSubstn[] [(lO',lO0)]
o0sub  = jSubstn[] [(lO,lO0)]
\end{code}


We need to be able to specify that a term variable $P$
is a standard UTP predicate in that defines a homogenous relation 
using dynamic observables ($O \cup O'\supseteq_a P$):
\begin{code}
isUTPDynObs  :: GenVar -> SideCond
isUTPDynObs  gP  = [gO,gO'] `dyncover` gP
areUTPDynObs :: [GenVar] -> SideCond
areUTPDynObs gPs = mrgscs $ map isUTPDynObs gPs
\end{code}
We also want to be able to specify that a term variable $c$
is a UTP condition ($O \supseteq_a c$):
\begin{code}
isUTPCond  :: GenVar -> SideCond
isUTPCond  gc  = [gO] `dyncover` gc
areUTPCond :: [GenVar] -> SideCond
areUTPCond gcs = mrgscs $ map isUTPCond gcs
\end{code}
We also need to specify a term variable $S$ 
that only contains static observables:
($O \cup O'\disj S$):
\begin{code}
isUTPStcObs  :: GenVar -> SideCond
isUTPStcObs  gS  = [gO,gO'] `notin` gS
areUTPStcObs :: [GenVar] -> SideCond
areUTPStcObs gSs = mrgscs $ map isUTPStcObs gSs
\end{code}

