\section{Universal Quantification (For-All)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module ForAll (
  forallName, forallTheory
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
import TestRendering
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
One thing that is missing is an axiom that allows us to remove quantifiers
from closed terms. The law \CJAllTrueN\ needs to be generalised to closed $P$,
and it then becomes a conjecture.
$$
\AXPREDGS
$$

What seems
\subsection{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
expression variable $e$,
and a useful collection of generic binder variables: $x,y,\lst x,\lst y$.

\subsubsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
gvP = StdVar vP
p = fromJust $ pVar vP
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] [] ; gves = LstVar lves
e = fromJust $ eVar ArbType ve
vf = Vbl (fromJust $ ident "f") ExprV Static
lvfs = LVbl vf [] [] ; gvfs = LstVar lvfs
f = fromJust $ eVar ArbType vf
\end{code}


\subsubsection{Generic Variables}

\begin{code}
vx = Vbl (fromJust $ ident "x") ObsV Static ; x = StdVar vx
tx = fromJust $ eVar ArbType vx
lvxs = LVbl vx [] [] ; xs = LstVar lvxs
vy = Vbl (fromJust $ ident "y") ObsV Static ; y = StdVar vy
lvys = LVbl vy [] [] ; ys = LstVar lvys
vz = Vbl (fromJust $ ident "z") ObsV Static ; z = StdVar vz
lvzs = LVbl vz [] [] ; zs = LstVar lvzs
\end{code}

\subsubsection{Substitutions}

\begin{code}
mksub p lvlvs = Sub P p $ fromJust $ substn [] lvlvs
esxs = [(lvxs,lves)]
ysxs = [(lvxs,lvys)]
fszs = [(lvzs,lvfs)]
efsyzs = [(lvys,lves),(lvzs,lvfs)]
\end{code}

\newpage
\subsection{Predicate Axioms}

$$
  \begin{array}{lll}
     \AXAllRemove & \AXAllRemoveS & \AXAllRemoveN
  \end{array}
$$

\vspace{-5pt}
\begin{code}
axAllRemove = preddef ("forall" -.- "remove")
                    (forall [xs] p  ===  p)
                    ([xs] `notin` gvP)
\end{code}

$$\begin{array}{lll}
   \AXAllOnePoint & \AXAllOnePointS & \AXAllOnePointN
\end{array}$$\par\vspace{-5pt}
\begin{code}
axAllOne = preddef ("forall" -.- "one" -.- "point")
  ( (forall [xs,ys] ((lvxs `areEqualTo` lves) ==> p) )
    ===
    (forall [ys] (mksub p esxs)) )
  ([xs] `notin` gves)
\end{code}

$$
  \begin{array}{lll}
  \\ \AXallODistr   & & \AXallODistrN
  \end{array}
$$\par\vspace{-4pt}
\begin{code}
axAllAndDistr = preddef ("forall" -.- "land" -.- "distr")
  ( (forall [xs] (p /\ q)) === (forall [xs] p) /\ (forall [xs] q) )
  scTrue
\end{code}

$$
  \begin{array}{lll}
     \AXorAllOScopeL \equiv \AXorAllOScopeR
                   & \AXorAllOScopeS & \AXorAllOScopeN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axOrAllScope = preddef ("lor" -.- "forall" -.- "scope")
  ( p \/ (forall [xs,ys] q)
    === forall [xs] ( p \/ forall [ys] q) )
  ([xs] `notin` gvP)
\end{code}


$$
  \begin{array}{lll}
    \AXAllOInst    &   & \AXAllOInstN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAllInst = preddef ("forall" -.- "inst")
  ( (forall [xs,ys] p)
    ==>
    (forall [ys] (mksub p esxs)) )
  scTrue
\end{code}


$$
  \begin{array}{lll}
     \AXAllDummyRen & \AXAllDummyRenS & \AXAllDummyRenN
  \end{array}
$$\par

\vspace{-8pt}
\begin{code}
axAllDumRen = preddef ("forall" -.- "alpha" -.- "rename")
  ( (forall [xs] p)
    ===
    (forall [ys] (mksub p ysxs)) )
  ([ys] `notin` gvP)
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
% \end{code}

We now collect all of the above as our axiom set:
\begin{code}
forallAxioms :: [Law]
forallAxioms
  = map labelAsAxiom
      [ axAllRemove, axAllOne, axAllAndDistr
      , axOrAllScope, axAllInst, axAllDumRen
      ]
\end{code}

\subsection{Predicate Conjectures}

$$
  \begin{array}{lll}
     \CJAllTrue &  \CJAllTrueN &
  \end{array}
$$

\vspace{-5pt}
\begin{code}
cjAllTrue = preddef ("forall" -.- "true")
                    (forall [xs] trueP  ===  trueP)
                    scTrue
\end{code}

We now collect our conjecture set:
\begin{code}
forallConjs :: [NmdAssertion]
forallConjs
  = [ cjAllTrue ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
forallName :: String
forallName = "ForAll"
forallTheory :: Theory
forallTheory
  =  nullTheory { thName  =  forallName
            , thDeps  =  [ equalityName
                         , implName
                         , aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , laws    =  forallAxioms
            , conjs   =  forallConjs
            }
\end{code}
