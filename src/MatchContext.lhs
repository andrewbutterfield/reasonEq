\chapter{Matching Contexts}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018-2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module MatchContext
 ( MatchContext
 , buildMatchContext
 , expandSCKnowns
 ) where

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import YesBut 
import Utilities
import WriteRead
import LexBase
import Variables
import AST
import SideCond
import Assertions
import TermZipper
import VarData
import Binding
import Matching
import AlphaEquiv
import Instantiate
import Laws
import Proofs
import Theories
import Sequents

import Symbols
import TestRendering

import Debugger
\end{code}

\newpage
\section{Matching Contexts}

Consider a collection of theories in an ordered list,
where each theory appears in that list before any of those on which
it depends.
Matching a conjecture component against all of these laws
means working through the theories, from first to last.
When working with a given theory, we want to match against
all the laws in that theory, using every variable-data table
in that theory and its dependencies.
In particular, if a pattern variable occurs in more than one var-table,
then we want the data from the first such table.

So given that we are matching in the context of a list of dependency-ordered
theories, we want to use a corresponding list of match contexts,
one for each theory.
A match context for a theory contains all the laws of that theory,
along with a dependency-ordered list of the var-tables,
including that of the theory itself,
as well as those from all subsequent theories.
\begin{code}
type MatchContext
  = ( String       -- Theory Name
    , [Law]        -- all laws of this theory
    , [VarTable] ) -- all known variables here, and in dependencies
\end{code}

Given a list of theories, we generate a list of match-contexts:
\begin{code}
buildMatchContext :: [Theory] -> [MatchContext]
buildMatchContext [] = []
buildMatchContext [thy] = [ (thName thy, laws thy, [known thy]) ]
buildMatchContext (thy:thys) -- thys not null
  = let mcs'@((_,_,vts'):_) = buildMatchContext thys
    in (thName thy, laws thy, known thy : vts') : mcs'
\end{code}

Expanding Known Variables in Side-Conditions
\begin{code}
expandSCKnowns :: [MatchContext] -> SideCond -> SideCond
expandSCKnowns mcs sc = sc
\end{code}


