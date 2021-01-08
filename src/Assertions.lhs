\section{Assertions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2021

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Assertions (
  Assertion
) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import LexBase
import Variables
import AST
import SideCond

import Test.HUnit hiding (Assertion)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}


\newpage
\subsection{Introduction}


An assertion is a \emph{normalised} predicate term coupled with side-conditions.
\begin{code}
type Assertion = (Term, SideCond)
\end{code}
