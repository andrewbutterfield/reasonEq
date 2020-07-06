\section{UTP Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPSignature (
  bookdef
, apred1, apred11, apred2
, i_refines, refines
, i_cond, cond
, i_seq, mkSeq
, i_asg, (.:=)
, i_skip, skip
, i_ndc, ndc
, i_abort, abort
, i_miracle, miracle
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


\begin{code}
i_t = jId "t"
tvar = TypeVar i_t
i_tn n = jId ("t"++show n)
tnvar n = TypeVar $ i_tn n
apred1 = FunType tvar bool
apred11 = FunType tvar apred1
apred2 = FunType (tnvar 1) $ FunType (tnvar 2) bool
\end{code}

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
i_refines    =  jId "sqsupseteq"
refines p q  =  PCons i_refines [p, q]

cond :: Term -> Term -> Term -> Term
i_cond       =  jId "cond"
cond p b q   =  PCons i_cond [p, b, q]

mkSeq :: Term -> Term -> Term
i_seq        =  jId ";"
mkSeq p q    =  PCons i_seq [p, q]

(.:=) :: Identifier -> Term -> Term
i_asg        =  jId ":="
v .:= e      =  PCons i_asg [jVar (E ArbType) (ExprVar v Static), e]

skip :: Term
i_skip  =  jId "II"
skip    =  jVar P $ Vbl i_skip PredV Static

ndc :: Term -> Term -> Term
i_ndc    =  jId "sqcap"
ndc p q  =  PCons i_ndc [p, q]

abort :: Term
i_abort  =  jId "bot"
abort    =  jVar P $ Vbl i_abort PredV Static

miracle :: Term
i_miracle  =  jId "top"
miracle    =  jVar P $ Vbl i_miracle PredV Static
\end{code}
