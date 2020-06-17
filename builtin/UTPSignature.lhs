\section{UTP Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPSignature (
  cond, mkSeq
) where

import Data.Maybe
import qualified Data.Set as S

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import FreeVars (normaliseQuantifiers)
import SideCond
import VarData
import Laws
import Proofs
import Theories
import TestRendering
\end{code}


\subsection{Introduction}

To be done


\subsection{Propositional Infrastructure}


We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$.

\subsubsection{Propositional Variables}

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}


\subsection{Base Language Operators}

\begin{code}
cond p b q  =  PCons (fromJust $ ident "cond") [p, b, q]
mkSeq p q   =  PCons (fromJust $ ident ";"   ) [p, q]
\end{code}
