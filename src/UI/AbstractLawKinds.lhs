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

import TestRendering
import SourceHandling

import StdTypeSignature

import Debugger
\end{code}

\section{Introduction}

This module provides the abstract functions for implementing automated proving 
based on law classifications.

\textbf{Important:} \emph{Nothing in this module should do IO of any kind}

This is \emph{very} tentative \dots
\begin{code}
applyCLA :: MonadFail mf => LiveProof -> mf LiveProof
applyCLA liveproofs = fail "Automating classifiers under development"
\end{code}


