\chapter{Matching Contexts}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module MatchContext
 ( MatchContext
 , buildMatchContext
 , getVarTables
 , expandSideCondKnownVars         
 , expandSCKnowns
 ) where

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import NotApplicable
import YesBut 
import Utilities
import WriteRead
import LexBase
import Variables
import AST
import VarSetPred
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

We commonly want to get all the \h{VarTables}s 
found in a list of match-contexts:
\begin{code}  
getVarTables :: [MatchContext] -> [VarTable]
-- old version: getVarTables = concat . map thd3
--new version  
getVarTables [] = []
getVarTables (mc:_) = thd3 mc
\end{code}

\newpage
\section{Expanding Knowns in Side-Conditions}

\begin{code}
expandSideCondKnownVars :: [MatchContext] -> SideCond -> SideCond
expandSideCondKnownVars [] sc = sc
expandSideCondKnownVars ((_,_,vts):_) sc  =  expandSCKnowns vts sc

expandSCKnowns :: [VarTable] -> SideCond -> SideCond
expandSCKnowns vts (SCD vscs freshvs)
  = SCD (concat $ map (expandVSCKnowns vts) vscs) 
        (mapVToverVarSet vts freshvs ) 

expandVSCKnowns :: [VarTable] -> VSetPred -> [VSetPred]
expandVSCKnowns vts  (VSDisj gv vset) 
  = buildVSCS VSDisj (expandVSCGenVar vts gv) (mapVToverVarSet vts vset)
expandVSCKnowns vts  (VSSub gv vset) 
  = buildVSCS VSSub  (expandVSCGenVar vts gv) (mapVToverVarSet vts vset)
expandVSCKnowns vts  (VSSubD gv vset) 
  = buildVSCS VSSubD (expandVSCGenVar vts gv) (mapVToverVarSet vts vset)
expandVSCKnowns vts vsp  =  [vsp]
\end{code}
We have $g~rel~vs$, 
but expansion (if $g$ is a list-variable)
may replace $g$ by $g_1,\dots,g_n$, where $n \geq 0$.
So we need to rely on the following laws:
\begin{eqnarray*}
   G_1 \cup G_2 \disj V &\equiv& G_1 \disj V \land G_2 \disj V
\\ G_1 \cup G_2 \subseteq V &\equiv& G_1 \subseteq V \land G_2 \subseteq V
\end{eqnarray*}
\begin{code}
expandVSCGenVar :: [VarTable] -> GenVar -> [GenVar]
expandVSCGenVar vts gv = S.toList $ mapVToverVarSet vts $ S.singleton gv

buildVSCS :: (GenVar -> VarSet -> VSetPred) 
          -> [GenVar] -> VarSet -> [VSetPred]
buildVSCS cons gvs vset = map (flip cons vset) gvs
\end{code}


