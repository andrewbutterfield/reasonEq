\section{Match Scenarios}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module MatchScenarios ( tst_match_scenarios ) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub)

import Test.HUnit
import Test.Framework as TF (testGroup, Test)
--import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import LexBase
import AST
import VarData
import Binding
import Matching
\end{code}

We create high-level matching scenarios to test the
fitness for purpose of the matching algorithms.
We place particular emphasis on UTP-specific matching requirements.


\begin{code}
tst_match_scenarios :: [TF.Test]

tst_match_scenarios
  = [ testGroup "\nMatching Scenarios"
      [ testCase "1+1=2 - succeeds" (1+1 @?= 2)
      , testCase "2+2=5 - fails" (2+2 @?= 5)
      ]
    ]
\end{code}
