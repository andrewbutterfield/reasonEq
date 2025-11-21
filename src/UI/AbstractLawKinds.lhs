\chapter{Abstract Law-Kinds}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2025
 
LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.AbstractLawKinds
( applyCLA
)
where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Char
import Data.Maybe
import Data.List
import Control.Applicative

import NotApplicable
import YesBut
import Utilities
import UnivSets
import LexBase
import Variables
import SideCond
import Assertions
import Laws
import TermZipper
import Types
import AST
import FreeVars
import AlphaEquiv
import Substitution
import Binding
import VarData
import MatchContext
import Typing
import Instantiate
import Sequents
import ProofSettings
import REqState
import Persistence
import ProofMatch
import Ranking
import SAT
import UI.AbstractProver

import TestRendering
import SourceHandling

import StdTypeSignature

import Debugger
\end{code}

\section{Introduction}

This module provides the abstract functions for implementing automated proving 
based on law classifications (\textit{a.k.a.} kinds).

The overall task breaks down into two main components:
\begin{itemize}
    \item 
      The first implements taking a law 
      and searching through the current proof goal 
      to find a sub-term to which it applies (if any).
    \item 
      The second is about having various collections of laws, 
      grouped by kinds, 
      and how to automate their use in some systematic way 
      to make progress in proofs.
\end{itemize}

\section{Basic Abstract Steps}

\begin{verbatim}
moveFocusDown :: MonadFail m => Int -> LiveProof -> m LiveProof
moveFocusUp :: MonadFail m => LiveProof -> m LiveProof

matchFocusAgainst :: MonadFail m => String -> LiveProof -> m LiveProof

applyMatchToFocus1 :: MonadFail m => 
  Int -> LiveProof -> m (ProofMatch,[Variable],[Term],[ListVar],VarList)

applyMatchToFocus2 :: MonadFail m => 
  [VarTable] -> ProofMatch ->
  [(Variable,Term)] -> [(ListVar,VarList)] -> VarList -> 
  LiveProof -> m LiveProof
\end{verbatim}
Function \h{applyMatchToFocus1} is run first,
then the user may be asked to make some choices,
and finally \h{applyMatchToFocus1} is called with the resulting choices.
The overall effect has type 
\verb"MonadFail m => Int -> LiveProof -> m LiveProof".


\section{Abstract Commands}

\textbf{Important:} \emph{Nothing in this module should do IO of any kind}

This is \emph{very} tentative \dots
\begin{code}
applyCLA :: MonadFail mf => LiveProof -> mf LiveProof
applyCLA liveproofs = fail "Automating classifiers under development"

-- this tests that we can call reference `moveFocusDown` from here
mFD :: MonadFail mf => Int -> LiveProof -> mf LiveProof
mFD = moveFocusDown 
\end{code}

\section{Law Application within a term}

\section{Applying Law Collections}


