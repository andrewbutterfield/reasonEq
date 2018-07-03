\section{Theories}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Theories
 ( Theory(..)
 , proofs__, proofs_
 , Theories
 , addTheory
 , getTheoryDeps
 , showTheories
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.List
--
import Utilities
import LexBase
import Variables
import AST
import SideCond
import TermZipper
import VarData
import Binding
import Matching
import Instantiate
import Proof
-- import Builder
--
import NiceSymbols
import TestRendering
--
-- import Test.HUnit hiding (Assertion)
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for single theories,
and structured collections of same.


\newpage
\subsection{Theories}

A theory is a collection of laws linked
to information about which variables in those laws are deemed as ``known''.
In addition we also keep a list of conjectures,
that will become laws if they ever have a proof.
We also allow a theory to depend on other theories,
so long as there are no dependency cycles.
\begin{code}
data Theory
  = Theory {
      thName      :: String
    , thDeps      :: [String] -- by name !
    , knownVars   :: VarTable
    , laws        :: [Law]
    , conjectures :: [NmdAssertion]
    , proofs      :: [Proof]
    }
  deriving (Eq,Show,Read)

proofs__ f r = r{proofs = f $ proofs r} ; proofs_ = proofs__ . const
\end{code}

We keep a collection of theories as a map,
indexed by their names:
\begin{code}
type Theories = Map String Theory

addTheory :: Monad m => Theory -> Theories -> m Theories
addTheory thry theories
 | nm `M.member` theories  =  fail ("Theory '"++nm++"' already present")
 | otherwise  =  do allDepsIn $ thDeps thry
                    return $ M.insert nm thry theories
 where
   nm = thName thry
   allDepsIn [] = return ()
   allDepsIn (thd:thds)
     | thd `M.member` theories  =  allDepsIn thds
     | otherwise  =  fail ("Dep. '"++thd++"' of theory '"++nm++"' not present")
\end{code}

We also need to generate a list of theories from the mapping,
given a starting point:
\begin{code}
getTheoryDeps :: Monad m => String -> Theories -> m [Theory]
getTheoryDeps nm theories
  = case M.lookup nm theories of
      Nothing  ->  fail "Top Theory not found"
      Just top
        ->  do deps <- getDeps theories (thDeps top)
               return (top:deps)

getDeps :: Monad m => Theories -> [String] -> m [Theory]
getDeps _ []  =  return []
getDeps theories (dnm:drest)
 = case M.lookup dnm theories of
     Nothing  ->  fail ("Dep '"++dnm++"' not found")
     Just thry
      -> let deps = thDeps thry
         in if null deps
             then do thrys <- getDeps theories drest
                     return (thry:thrys)
             else do thrys <- getDeps theories $ nub (deps ++ drest)
                     return (thry:thrys)
\end{code}


\newpage
\subsection{Showing stuff}

\textbf{This should all be done via proper generic rendering code}


Showing theories:
\begin{code}
showTheories thrys = showTheories' $ M.assocs thrys
showTheories' [] = "No theories present."
showTheories' thrys = unlines' $ map (showTheory . snd) thrys

showTheory thry
  = unlines (
      ( "Theory '"++thName thry++"'" )
      : if null deps
        then []
        else [ "depends on: "++intercalate "," (thDeps thry)]
      ++
      [ trVarTable (knownVars thry)
      , showLaws (laws thry) ]
    )
  where deps = thDeps thry
\end{code}
