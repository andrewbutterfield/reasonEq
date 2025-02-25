\chapter{Top GUI}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2017--25
              Saqid Zardari      2023
              Aaron Bruce        2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module TopGUI where

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

import ProgramIdentity
import LexBase
import Variables
import AST
import VarData
import Binding
import Typing
import SideCond
import Assertions
import Ranking
import REqState
import AbstractUI
import UTPWhileRefineSig
import Instantiate
import TestRendering
import Parsing
import REPL
import Dev
import SAT
import Classifier
import LiveProofs
import TopTUI

import Debugger
\end{code}


\section{GUI Top-Level}

The GUI has yet to be developed but will probably
use \texttt{threepenny-gui} along with the Electron browser.
\begin{code}
gui :: REqState -> IO ()
gui reqs0 = do putStrLn "GUI not implemented, using command-line."
               tui reqs0
\end{code}

