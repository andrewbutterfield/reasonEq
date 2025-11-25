\chapter{Law-Kind TUI}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.LawKindTUI (
  doClassDrivenAutomation, applyACLDescr
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
import Instantiate
import TestRendering
import SourceHandling
import Dev
import SAT
import Classifier
import ProofMatch
import UI.AbstractProver
import UI.AbstractLawKinds
import UI.REPL
import UI.TSupport

import Debugger
\end{code}

\section{Introduction}

This module provides the text user interface for using automated proving based 
on law classifications.

The key idea is that we have collections of different kinds of laws
(\textit{e.g.}, simplifiers, fold/unfold, \dots),
and we want some form of automation that will try to 
use laws of a given kind to make progress.
When one law kind stops making progress, we will choose another kind.
We keep repeating this until no laws of any kind have any effect.

In a little more detail:
\begin{itemize}
  \item 
    Applying a law to a proof goal will involve searching the proof goal
    to find a sub-term of the goal where the law matches.
    If such a term is found, 
    we then return the proof goal with that sub-term replaced by the result of
    the match.
  \item
    Given a collection of laws of the same kind,
    we simply try to apply each such law to the proof goal.
    We terminate if a law suceeds in making a change,
    or if we have tried all laws in the collection.
  \item
    Given several such collections, we try each collection in turn.
    Whenever a collection fails to change the goal, 
    we switch to the next collection.
    When a complete run through of all laws in all collections 
    results in no change, we terminate.
\end{itemize}


\newpage
\section{Basic TUI Steps}

All have type \h{REPLCmd (REqState, LiveProof)},
and are defined in \h{ProverTUI}.
\begin{verbatim}
tryDelta . moveFocusDown
tryDelta . moveFocusUp 
tryDelta . (matchFocus ranking) -- matchLawCommand + ranking
applyMatchToFocus1
\end{verbatim}

The follwing shows that these are visible here:
\begin{code}
tD_mFD :: Monad m => Int -> (a,LiveProof) -> m (a,LiveProof)
tD_mFD i s = tryDelta (moveFocusDown i) s

tD_mFU :: Monad m => (a,LiveProof) -> m (a,LiveProof)
tD_mFU s = tryDelta (moveFocusUp) s

-- mLC = matchLawCommand
\end{code}



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

\begin{code}
acl = "automate classified laws"
applyACLDescr = ("acl"
                , acl
                , unlines'
                   [ "Invokes automatic application of classified laws"
                   , "to the focus and its sub-terms." ]
                , doClassDrivenAutomation)
\end{code}
\textbf{NOTE:}
Any new commands need to have their equivalent \h{applyACLDescr}
added to the long list in \h{ProverTUI.proofREPLConfig}.


\textbf{Important:} \emph{Any steps requiring user input need to occur here}

It might help to several commands here
\begin{itemize}
  \item Apply one law to the proof goal
  \item Apply a collection of laws to the proof goal
  \item Apply several law collections to the proof goal
\end{itemize}

