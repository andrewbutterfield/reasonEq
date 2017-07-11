\section{Concrete Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Builder ( int_tst_Builder
               ) where
--import Data.Maybe (fromJust)
--import qualified Data.Map as M

--import Utilities
--import LexBase
import AST
import Syntax

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{Term Building}

Here we provide ways to build terms.

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_Builder :: [TF.Test]
int_tst_Builder
 = [ testGroup "\nBuilder Internal"
     [ testCase "1+1=2"  (1+1 @?= 2)]
   ]
\end{code}
