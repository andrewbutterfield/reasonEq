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
, listwiseVarBinPred
, i_asg, (.:=), (.::=), simassign
, i_skip, skip
, i_ndc, ndc
, i_abort, abort
, i_miracle, miracle
) where

import Data.Maybe
import qualified Data.Set as S

import NiceSymbols

import Control (mapsnd)
import Utilities
import LexBase
import Variables
import AST
import Assertions (mkAsn)
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

\subsubsection{Refinement}
$$ P \sqsupseteq Q $$
\begin{code}
refines :: Term -> Term -> Term
i_refines    =  jId "sqsupseteq"
refines p q  =  PCons False i_refines [p, q]
\end{code}

\subsubsection{Conditionals}
$$ P \cond b Q $$
\begin{code}
cond :: Term -> Term -> Term -> Term
i_cond       =  jId "cond"
cond p b q   =  PCons True i_cond [p, b, q]
\end{code}

\subsubsection{Sequential Composition}
$$ P \seq Q $$
\begin{code}
mkSeq :: Term -> Term -> Term
i_seq        =  jId ";"
mkSeq p q    =  PCons False i_seq [p, q]
\end{code}

\subsubsection{(Simultaneous) Assignement}
$$ \lst x := \lst e $$
\begin{code}
listwiseVarBinPred :: TermKind -> Identifier -> Identifier
                    -> [(Variable,Variable)] -> [(ListVar,ListVar)] -> Term
listwiseVarBinPred tk na ni vvs lvlvs
  | null vvs    =  doiter lvlvs
  | null lvlvs  =  docons vvs
  | otherwise   =  Cons tk True na [docons vvs,doiter lvlvs]
  where
    docons [vv]       =  mkcons vv
    docons vvs        =  Cons tk True na $ map mkcons vvs
    mkcons (v1,v2)    =  Cons tk True ni [varAsTerm v1,varAsTerm v2]
    doiter [lvlv]     =  mkiter lvlv
    doiter lvlvs      =  Cons tk True na $ map mkiter lvlvs
    mkiter (lv1,lv2)  =  Iter tk True na True ni [lv1,lv2]

simassign :: [(Variable,Term)] -> [(ListVar,ListVar)] -> Term
simassign vts lvlvs  =  Sub P p_asg $ jSubstn vts lvlvs

(.:=) :: Variable -> Term -> Term
i_asg        =  jId ":="
p_asg        =  jVar P $ Vbl i_asg PredV Static
v .:= e      =  simassign [(v,e)] []

(.::=) :: ListVar -> ListVar -> Term
lv .::= le   =  simassign [] [(lv,le)]
\end{code}

\subsubsection{Skip}
$$ \Skip $$
\begin{code}
skip :: Term
i_skip  =  jId "II"
skip    =  jVar P $ Vbl i_skip PredV Static
\end{code}

\subsubsection{Non-deterministic Choice}
$$ P \sqcap Q $$
\begin{code}
ndc :: Term -> Term -> Term
i_ndc    =  jId "sqcap"
ndc p q  =  PCons True i_ndc [p, q]
\end{code}

\subsubsection{Abort and Miracle}
$$ \bot \qquad \top $$
\begin{code}
abort :: Term
i_abort  =  jId "bot"
abort    =  jVar P $ Vbl i_abort PredV Static

miracle :: Term
i_miracle  =  jId "top"
miracle    =  jVar P $ Vbl i_miracle PredV Static
\end{code}
