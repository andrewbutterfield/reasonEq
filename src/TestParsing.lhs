\section{Test Parsing}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TestParsing

where

-- import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
-- import qualified Data.Set as S
-- import Data.List (nub, sort, (\\), intercalate)
-- import Data.Char

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import TestRendering
\end{code}

\subsection{Test Parsing Intro.}

We provide a simple, clunky way to parse terms,
in prefix-style only.
