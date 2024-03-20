\chapter{Linear Temporal Logic}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LTL (
  ltlName, ltlTheory
) where

import Data.Maybe
import qualified Data.Set as S

import Symbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Theories

import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import Implication
import Equality
import ForAll
import Exists
import TestRendering
import StdTypeSignature
\end{code}


\newpage
\section{Introduction}


Here we present a hard-coded implementation of
linear temporal logic using equational reasoning
\cite{DBLP:journals/csur/WarfordVS20}.
This is based on Gries \& Schneider\cite{gries.93}
and Tourlakis \cite{journals/logcom/Tourlakis01}.

\section{LTL Signature}

\def\next{\mathop{\circ}}
\def\eventually{\mathop{\diamond}}
\def\always{\mathop{\smallsquare}}
\def\until{\mathop{\mathcal{U}}}
\def\wuntil{\mathop{\mathcal{W}}}

We have the following additional logic operators in LTL:
$\next~\eventually~\always~\until~\wuntil$.

We have the following precedences in \cite{DBLP:journals/csur/WarfordVS20},
from high to low:
\begin{eqnarray*}
\\ && [x:=e]
\\ && \lnot \quad \next \quad \eventually \quad \always 
\\ && \until \quad \wuntil
\\&& =
\\&& \lor \quad \land
\\&& \implies \quad \Longleftarrow
\\&& \equiv
\end{eqnarray*}

\begin{code}
theN = jId "next"       ; mkN p   = Cons arbpred True theNext       [p]
theE = jId "eventually" ; mkE p   = Cons arbpred True theEventually [p]
theA = jId "always"     ; mkA p   = Cons arbpred True theA          [p]
theU = jId "until"      ; mkU p q = Cons arbpred True theU        [p,q]
theW = jId "wuntil"     ; mkW p q = Cons arbpred True theW        [p,q]
\end{code}


\section{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
expression variable $e$,
and a useful collection of generic binder variables: $x,y,\lst x,\lst y$.

\subsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
gvP = StdVar vP
p = fromJust $ pVar ArbType vP
q = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "R") PredV Static
ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] [] ; gves = LstVar lves
e = fromJust $ eVar ArbType ve
vf = Vbl (fromJust $ ident "f") ExprV Static
lvfs = LVbl vf [] [] ; gvfs = LstVar lvfs
f = fromJust $ eVar ArbType vf
\end{code}


\subsection{Generic Variables}

\begin{code}
vx = Vbl (fromJust $ ident "x") ObsV Static ; x = StdVar vx
tx = fromJust $ eVar ArbType vx
lvxs = LVbl vx [] [] ; xs = LstVar lvxs
vy = Vbl (fromJust $ ident "y") ObsV Static ; y = StdVar vy
lvys = LVbl vy [] [] ; ys = LstVar lvys
vz = Vbl (fromJust $ ident "z") ObsV Static ; z = StdVar vz
lvzs = LVbl vz [] [] ; zs = LstVar lvzs
\end{code}

\subsection{Substitutions}

\begin{code}
mksub p lvlvs = Sub pred1 p $ fromJust $ substn [] lvlvs
esxs = [(lvxs,lves)]
ysxs = [(lvxs,lvys)]
fszs = [(lvzs,lvfs)]
efsyzs = [(lvys,lves),(lvzs,lvfs)]
\end{code}

\newpage
\section{Predicate Axioms}


% %% TEMPLATE
% $$
%   \begin{array}{lll}
%      law & sc & name
%   \end{array}
% $$\par
%
%\vspace{-8pt}
% \begin{code}
% axXXX = preddef ("law" -.- "name")
%   p
%   scTrue
% \end{code}

We now collect all of the above as our axiom set:
\begin{code}
ltlAxioms :: [Law]
ltlAxioms
  = map labelAsAxiom
      [ 
      ]
\end{code}

\section{Predicate Conjectures}


We now collect our conjecture set:
\begin{code}
ltlConjs :: [NmdAssertion]
ltlConjs
  = [  ]
\end{code}


\section{The Predicate Theory}

\begin{code}
ltlName :: String
ltlName = "LTL"
ltlTheory :: Theory
ltlTheory
  =  nullTheory { thName  =  ltlName
            , thDeps  =  [ equalityName
                         , existsName
                         , forallName
                         , implName
                         , aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , laws    =  ltlAxioms
            , conjs   =  ltlConjs
            }
\end{code}
