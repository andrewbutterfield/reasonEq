\section{Predicate Axioms}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PredAxioms (
  forall, exists
, predAxioms, predAxiomName, predAxiomTheory
) where

import Data.Maybe
import qualified Data.Set as S

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Theories

import PropAxioms
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropMixOne
import PropImpl
import Equality
\end{code}


\newpage
\subsection{Introduction}


Here we present a hard-coded implementation of
predicate equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
However we adopt here a formulation closer to that of Gries\&Schneider,
as the Tourlakis form has useful laws such as the one-point rules
derived from his axioms by meta-proofs
\emph{that use non-equational reasoning}.
$$
\AXPREDGS
$$

\subsection{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
expression variable $e$,
the constants $\forall$ and $\exists$,
and a useful collection of generic binder variables: $x,y,\lst x,\lst y$.

\subsubsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
p = fromJust $ pVar vP
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] []
e = fromJust $ eVar ArbType ve
\end{code}

\subsubsection{Predicate Constants}

\begin{code}
forallId = fromJust $ ident _forall
forallV = Vbl forallId PredV Static
forall vl p = fromJust $ pBind forallId (S.fromList vl) p
existsId = fromJust $ ident _exists
existsV = Vbl existsId PredV Static
exists vl p = fromJust $ pBind existsId (S.fromList vl) p
\end{code}

\subsubsection{Generic Variables}

\begin{code}
vx = Vbl (fromJust $ ident "x") ObsV Static ; x = StdVar vx
tx = fromJust $ eVar ArbType vx
lvxs = LVbl vx [] [] ; xs = LstVar lvxs
vy = Vbl (fromJust $ ident "y") ObsV Static ; y = StdVar vy
lvys = LVbl vy [] [] ; ys = LstVar lvys
\end{code}


\newpage
\subsection{Predicate Axioms}

General predicates laws often have side-conditions:
\begin{code}
preddef name prop sc = ( name, ( prop, sc ) )
\end{code}

$$
  \begin{array}{lll}
     \AXAllTrue & \AXAllTrueN &
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAllTrue = preddef (_forall -.- "true")
                    (forall [xs] trueP  ===  trueP)
                    scTrue
\end{code}

$$\begin{array}{lll}
   \AXAllOnePoint & \AXAllOnePointS & \AXAllOnePointN
\end{array}$$\par\vspace{-8pt}
\begin{code}
axAllOne = preddef (_forall -.- "one" -.- "point")
  ( (forall [xs,ys] ((lvxs `areEqualTo` lves) ==> p) )
    ===
    (forall [xs] (Sub P p (fromJust $ substn [] [(lvxs,lves)])) ) )
  ([xs] `notin` ve)
\end{code}

$$
  \begin{array}{lll}
  \\ \AXallODistr   & & \AXallODistrN
  \end{array}
$$\par\vspace{-4pt}
\begin{code}
axAllAndDistr = preddef (_forall -.- _land -.- "distr")
  ( (forall [xs] (p /\ q)) === (forall [xs] p) /\ (forall [xs] q) )
  scTrue
\end{code}


%% TEMPLATE
$$
  \begin{array}{lll}
     \AXorAllOScopeL \equiv \AXorAllOScopeR
                   & \AXorAllOScopeS & \AXorAllOScopeN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axOrAllScope = preddef (_lor -.- _forall -.- "scope")
  p
  ([xs] `notin` vP)
\end{code}


$$
  \begin{array}{lll}
    \AXAllOInst    &   & \AXAllOInstN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAllInst = preddef (_forall -.- "inst") p scTrue
\end{code}


$$
  \begin{array}{lll}
     \AXAllDummyRen & \AXAllDummyRenS & \AXAllDummyRenN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAllDumRen = preddef (_forall -.- "dummy" -.- "rename")
  p
  ([ys] `notin` vP)
\end{code}

$$
  \begin{array}{lll}
     \AXanyODef & & \AXanyODefN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAnyDef = preddef (_exists -.- "def") p scTrue
\end{code}


% %% TEMPLATE
% $$
%   \begin{array}{lll}
%      law & sc & name
%   \end{array}
% $$\par\vspace{-8pt}
% \begin{code}
% axXXX = preddef ("law" -.- "name") p scTrue
% \end{code}

We now collect all of the above as our axiom set:
\begin{code}
predAxioms :: [Law]
predAxioms
  = map labelAsAxiom
      [ axAllTrue, axAllOne, axAllAndDistr
      , axOrAllScope, axAllInst, axAllDumRen
      , axAnyDef ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
predAxiomName :: String
predAxiomName = "PredAxioms"
predAxiomTheory :: Theory
predAxiomTheory
  =  Theory { thName  =  predAxiomName
            , thDeps  =  [ equalityName
                         , propImplName
                         , propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName ]
            , known   =  newVarTable
            , laws    =  predAxioms
            , proofs  =  []
            , conjs   =  []
            }
\end{code}
