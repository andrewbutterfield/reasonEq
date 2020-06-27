\section{UTP Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPSignature (
  bookdef
, refines
, cond, mkSeq, (.:=), skip, ndc
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
import StdSignature
\end{code}


\subsection{Introduction}

To be done

We want to map definition and law numbers
from the book to law names.
\begin{code}
bookdef :: String -> String -> Term -> SideCond
        -> (NmdAssertion, (String, String))
bookdef name alias prop sc
  = (preddef name prop sc,(alias,name))
\end{code}

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
refines :: Term -> Term -> Term
refines p q  =  PCons (jId "sqsupseteq") [p, q]

cond :: Term -> Term -> Term -> Term
cond p b q   =  PCons (jId "cond") [p, b, q]

mkSeq :: Term -> Term -> Term
mkSeq p q    =  PCons (jId ";"   ) [p, q]

(.:=) :: Identifier -> Term -> Term
v .:= e      =  PCons (jId ":=") [jVar (E ArbType) (ExprVar v Static), e]

skip :: Term
skip = jVar P $ Vbl (jId "II") PredV Static

ndc :: Term -> Term -> Term
ndc p q = PCons (jId "sqcap") [p, q]
\end{code}
