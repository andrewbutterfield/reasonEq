\section{UTP Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPSignature (
  bookdef
, i_refines, refines
, i_cond, cond
, i_seq, mkSeq
, i_while, while
, listwiseVarBinPred
, i_asg, (.:=), (.::=), simassign
, i_skip, skip, g_skip
, i_ndc, ndc
, i_abort, abort
, i_miracle, miracle
) where

import Data.Maybe
import qualified Data.Set as S

import Symbols

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
import StdTypeSignature
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
p = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "R") PredV Static
\end{code}


\subsection{Base Language Operators}

\subsubsection{Refinement}
$$ P \sqsupseteq Q $$
\begin{code}
refines :: Term -> Term -> Term
i_refines    =  jId "refines"
refines p q  =  Cons arbpred False i_refines [p, q]
\end{code}

\subsubsection{Conditionals}
$$ P \cond b Q $$
\begin{code}
cond :: Term -> Term -> Term -> Term
i_cond       =  jId "cond"
cond p b q   =  Cons arbpred True i_cond [p, b, q]
\end{code}

\subsubsection{Sequential Composition}
$$ P \seq Q $$
\begin{code}
mkSeq :: Term -> Term -> Term
i_seq        =  jId ";"
mkSeq p q    =  Cons arbpred False i_seq [p, q]
\end{code}

\subsubsection{While Loop}
$$ c \circledast P$$
\begin{code}
while :: Term -> Term -> Term
i_while = jId "while"
while c p = Cons arbpred False i_while [c, p]
\end{code}

\subsubsection{(Simultaneous) Assignement}
$$ \lst x := \lst e $$
\begin{code}
listwiseVarBinPred :: Type -> Identifier -> Identifier
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


p1 = arbpred
i_asg        =  assignmentId
p_asg        =  jVar p1 $ Vbl i_asg PredV Textual

simassign :: [(Variable,Term)] -> [(ListVar,ListVar)] -> Term
simassign vts lvlvs  =  Sub p1 p_asg $ jSubstn vts lvlvs

(.:=) :: Variable -> Term -> Term
v .:= e      =  simassign [(v,e)] []

(.::=) :: ListVar -> ListVar -> Term
lv .::= le   =  simassign [] [(lv,le)]
\end{code}

\subsubsection{Skip}
$$ \Skip $$
\begin{code}
skip :: Term
i_skip  =  jId "II"
v_skip  =  Vbl i_skip PredV Static
g_skip  =  StdVar v_skip
skip    =  jVar p1 v_skip 
\end{code}

\subsubsection{Non-deterministic Choice}
$$ P \sqcap Q $$
\begin{code}
ndc :: Term -> Term -> Term
i_ndc    =  jId "sqcap"
ndc p q  =  Cons arbpred True i_ndc [p, q]
\end{code}

\subsubsection{Abort and Miracle}
$$ \bot \qquad \top $$
\begin{code}
abort :: Term
i_abort  =  jId "bot"
abort    =  jVar p1 $ Vbl i_abort PredV Static

miracle :: Term
i_miracle  =  jId "top"
miracle    =  jVar p1 $ Vbl i_miracle PredV Static
\end{code}
