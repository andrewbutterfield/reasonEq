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


We have the following additional logic operators in LTL:
$\next~\eventually~\always~\until~\wait$.

We have the following precedences in \cite{DBLP:journals/csur/WarfordVS20},
from high to low:
\begin{eqnarray*}
\\ && [x:=e]
\\ && \lnot \quad \next \quad \eventually \quad \always 
\\ && \until \quad \wait
\\&& =
\\&& \lor \quad \land
\\&& \implies \quad \Longleftarrow
\\&& \equiv
\end{eqnarray*}

\begin{code}
theN = jId "next"       ; mkN p   = Cons arbpred True theN [p]
v_next = Vbl theN ObsV Static
theE = jId "eventually" ; mkE p   = Cons arbpred True theE [p]
v_event = Vbl theE ObsV Static
theA = jId "always"     ; mkA p   = Cons arbpred True theA [p]
v_always = Vbl theA ObsV Static
theU = jId "until"      ; mkU p q = Cons arbpred True theU [p,q]
v_until = Vbl theU ObsV Static
theW = jId "wait"       ; mkW p q = Cons arbpred True theW [p,q]
v_wait = Vbl theW ObsV Static
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


\section{Temporal Operators}

Based on \cite{DBLP:journals/csur/WarfordVS20}:
Given a set $V$ of variables, 
we define a state $s$ as a total mapping from the variables in $V$
to values in some appropriate domain.
We define a model $\sigma$ over $V$ as an infinite sequence of states:
$s_0,s_1,s_2,\dots$.
An anchored sequence $(\sigma,j)$ is such a sequence 
paired with an index $j$ that identifies $s_j$.
LTL entailment $(\sigma,j) \models p$ states 
that property $p$ holds \emph{at} position $j$ in $\sigma$.

\subsection{The Next Operator ($\next$)}

\begin{eqnarray*}
  (\sigma,j) \models \next p  &\IFF&  (\sigma,j+1) \models p
\end{eqnarray*}

$$
  \begin{array}{lll}
     \next \lnot p \equiv \lnot \next p &  & \QNAME{$\next$-self-dual}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
axNextSelfDual 
  = preddef ("next" -.- "self" -.- "dual")
            (mkN (mkNot p) === mkNot (mkN p))
            scTrue
\end{code}

$$
  \begin{array}{lll}
     \next \lnot p \equiv \lnot \next p &  & \QNAME{$\next$-$\implies$-distr}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
axNextImpliesDistr 
  = preddef ("next" -.- "implies" -.- "distr")
            (mkN (p ==> q) ===  mkN p ==> mkN q)
            scTrue
\end{code}

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
% cjYYY = ( "conj"-.-"name"
%         , (  p
%           , scTrue ) )
% \end{code}


\subsection{The Until Operator ($\until$)}

\begin{eqnarray*}
  (\sigma,j) \models p \until q  
  &\IFF&  
  \exists k \mid k \geq j \bullet
  (\sigma,k) \models q
  \land 
  (\forall i \mid j \leq i < k \bullet
  (\sigma,i) \models p)
\end{eqnarray*}

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
% cjYYY = ( "conj"-.-"name"
%         , (  p
%           , scTrue ) )
% \end{code}


\subsection{The Eventually Operator ($\eventually$)}

\begin{eqnarray*}
  (\sigma,j) \models \eventually p 
  &\IFF&  
  \exists k \mid k \geq j \bullet
  (\sigma,k) \models p
\end{eqnarray*}

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
% cjYYY = ( "conj"-.-"name"
%         , (  p
%           , scTrue ) )
% \end{code}


\subsection{The Always Operator ($\always$)}

\begin{eqnarray*}
  (\sigma,j) \models \always p 
  &\IFF&  
  \forall k \mid k \geq j \bullet
  (\sigma,k) \models p
\end{eqnarray*}

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
% cjYYY = ( "conj"-.-"name"
%         , (  p
%           , scTrue ) )
% \end{code}


\subsection{The Wait Operator ($\wait$)}

\begin{eqnarray*}
  (\sigma,j) \models p \wait q  
  &\IFF&  
  (\sigma,j) \models p \until q
  \quad\lor\quad 
  (\sigma,j) \models \always p
\end{eqnarray*}


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
% cjYYY = ( "conj"-.-"name"
%         , (  p
%           , scTrue ) )
% \end{code}


\section{LTL Theory Assembly}

\subsection{LTL Known Names}

\begin{code}
ltlKnown :: VarTable
ltlKnown  = fromJust $ addKnownVar v_next boolf_1 $
            fromJust $ addKnownVar v_event boolf_1 $
            fromJust $ addKnownVar v_always boolf_1 $
            fromJust $ addKnownVar v_until boolf_2 $ 
            fromJust $ addKnownVar v_wait boolf_2 $ 
            newVarTable

\end{code}

\subsection{LTL Axioms}

We now collect all of the above as our axiom set:
\begin{code}
ltlAxioms :: [Law]
ltlAxioms
  = map labelAsAxiom
      [ axNextSelfDual, axNextImpliesDistr
      ]
\end{code}

\subsection{LTL Conjectures}


We now collect our conjecture set:
\begin{code}
ltlConjs :: [NmdAssertion]
ltlConjs
  = [  ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
ltlName :: String
ltlName = "LTL"
ltlTheory :: Theory
ltlTheory
  = nullTheory  { thName  =  ltlName
                , thDeps  = [ equalityName
                            , existsName
                            , forallName
                            , implName
                            , aoiName
                            , conjName
                            , disjName
                            , notName
                            , equivName
                            ]
                , known = ltlKnown
                , laws  = ltlAxioms
                , conjs = ltlConjs
            }
\end{code}
