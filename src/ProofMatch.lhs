\chapter{Proof Match Data}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module ProofMatch( ProofMatch(..), Matches ) 
where

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import AST 
import SideCond 
import Binding 
import Proofs
import Sequents
\end{code}

\section{Proof Matches}

This data-structure records data about a law match needed by the prover.
\begin{code}
data ProofMatch
 = MT { mName    ::  String     -- assertion name
      , mAsn     ::  TermSC     -- matched assertion
      , mClass   ::  MatchClass -- match class
      , mBind    ::  Binding    -- resulting binding
      , mLawPart ::  Term       -- replacement term from law
      , mLocSC   ::  SideCond   -- goal side-condition local update
      , mLawSC   ::  SideCond   -- law side-condition mapped to goal
      , mRepl    ::  Term       -- replacement term, instantiated with binding
      } deriving (Eq,Show,Read)

type Matches = [ProofMatch]
\end{code}

