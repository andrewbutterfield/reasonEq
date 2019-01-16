\section{Existential Theorems}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PredExists (
  predExistsConjs, predExistsName, predExistsTheory
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
import PropSubst
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropMixOne
import PropImpl
import Equality
import PredAxioms
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
\CONJEXISTS
$$

\subsection{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
expression variable $e$,
the constants $\forall$, $\exists$, $[]$,
and a useful collection of generic binder variables: $x,y,\lst x,\lst y$.

\subsubsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
gvP = StdVar vP
p = fromJust $ pVar vP
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] []
gves = LstVar lves
e = fromJust $ eVar ArbType ve
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
\subsection{Existential Conjectures}

$$
  \begin{array}{lll}
     \CJAnyFalse & & \CJAnyFalseN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyTrue = preddef (_exists -.- "false")
                    (exists [xs] falseP  ===  falseP)
                    scTrue
\end{code}

$$\begin{array}{lll}
   \CJAnyOnePoint  & \CJAnyOnePointS  & \CJAnyOnePointN
\end{array}$$\par\vspace{-8pt}
\begin{code}
cjAnyOne = preddef (_exists -.- "one" -.- "point")
  ( (exists [xs,ys] ((lvxs `areEqualTo` lves) /\ p) )
    ===
    (exists [ys] (Sub P p (fromJust $ substn [] [(lvxs,lves)])) ) )
  ([xs] `notin` gves)
\end{code}

$$
  \begin{array}{lll}
  \\ \CJanyODistr & & \CJanyODistrN
  \end{array}
$$\par\vspace{-4pt}
\begin{code}
cjAnyOrDistr = preddef (_exists -.- _lor -.- "distr")
  ( (exists [xs] (p \/ q)) === (exists [xs] p) \/ (exists [xs] q) )
  scTrue
\end{code}

$$
  \begin{array}{lll}
     \CJandAnyOScope & \CJandAnyOScopeS & \CJandAnyOScopeN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAndAllScope = preddef (_land -.- _exists -.- "scope")
  ( p /\ (exists [xs,ys] q)
    === exists [xs] ( p /\ exists [ys] q) )
  ([xs] `notin` gvP)
\end{code}


$$
  \begin{array}{lll}
    \CJAnyOInst & & \CJAnyOInst
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyInst = preddef (_exists -.- "inst")
  ( (exists [ys] (Sub P p (fromJust $ substn [] [(lvxs,lves)])) )
    ==>
    (exists [xs,ys] p) )
  scTrue
\end{code}


$$
  \begin{array}{lll}
     \CJAnyDummyRen  & \CJAnyDummyRenS  & \CJAnyDummyRenN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyDumRen = preddef (_exists -.- _alpha -.- "rename")
  ( (exists [xs] p)
    ===
    (exists [ys] (Sub P p (fromJust $ substn [] [(lvxs,lvys)])) ) )
  ([ys] `notin` gvP)
\end{code}

% %% TEMPLATE
% $$
%   \begin{array}{lll}
%      law & sc & name
%   \end{array}
% $$\par\vspace{-8pt}
% \begin{code}
% axXXX = preddef ("law" -.- "name")
%   p
%   scTrue
% \end{code}

We now collect all of the above as our axiom set:
\begin{code}
predExistsConjs :: [NmdAssertion]
predExistsConjs
  = [ cjAnyTrue, cjAnyOne, cjAnyOrDistr
    , axAndAllScope, cjAnyInst, cjAnyDumRen ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
predExistsName :: String
predExistsName = "PredExists"
predExistsTheory :: Theory
predExistsTheory
  =  Theory { thName  =  predExistsName
            , thDeps  =  [ predAxiomName
                         , equalityName
                         , propSubstName
                         , propImplName
                         , propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName
                         ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  predExistsConjs
            }
\end{code}
