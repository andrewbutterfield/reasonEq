\chapter{Classifier TUI}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.ClassifierTUI (
  doClassDrivenAutomation
) 
where

import System.Environment
import System.IO
import System.FilePath
import System.Directory
import System.Exit
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char

import Symbols hiding (help)

import YesBut
import Utilities
import StratifiedDAG
import Persistence

import LexBase
import Variables
import AST
import VarData
import Binding
import Typing
import SideCond
import Assertions
import Ranking
import ProofSettings
import REqState
import MatchContext
import UI.AbstractClassifier
import Instantiate
import TestRendering
import SourceHandling
import UI.REPL
import Dev
import SAT
import Classifier
import ProofMatch

import Debugger
\end{code}

\section{Introduction}

This module provides the text user interface for using automated proving based 
on law classifications.



\section{TUI Commands}

For now there is one prover-level command:

\begin{code}
doClassDrivenAutomation :: REPLCmd (REqState, LiveProof)
doClassDrivenAutomation _ (reqs,liveproof)
  = case applyCLA liveproof of
      Yes liveproof' -> return (reqs, liveproof')
      But msgs -> do putStrLn $ unlines' msgs
                     waitForReturn
                     return (reqs, liveproof) 
\end{code}

(This may change)

\textbf{Important:} \emph{Any steps requiring user input need to occur here}
