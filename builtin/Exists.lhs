\chapter{Existential Quantification}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Exists (
  existsConjs, existsName, existsTheory
) where

import Data.Maybe
import qualified Data.Set as S

import Symbols

import Utilities
import LexBase
import Variables
import Types
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
import TestRendering
import StdTypeSignature
\end{code}


\newpage
\section{Introduction}


Here we present a hard-coded implementation of
predicate equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
However we adopt here a formulation closer to that of Gries\&Schneider,
as the Tourlakis form has useful laws such as the one-point rules
derived from his axioms by meta-proofs
\emph{that use non-equational reasoning}.
$$
\AXEXISTS
$$

$$
\CONJEXISTS
$$

\section{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
expression variable $e$,
the constants $\forall$, $\exists$, $[]$,
and a useful collection of generic binder variables: $x,y,\lst x,\lst y$.

\subsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
gvP = StdVar vP
p = fromJust $ pVar ArbType vP
q = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "R") PredV Static
ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] []
gves = LstVar lves
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
\section{Existential Axioms}

$$
  \begin{array}{lll}
     \AXanyODef & & \AXanyODefN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAnyDef = preddef ("exists" -.- "def")
  ( (exists [xs] p)
    ===
    (mkNot $ forAll [xs] $ mkNot p) )
  scTrue
\end{code}

We now collect our axiom:
\begin{code}
predExistsAxioms :: [Law]
predExistsAxioms
  = map labelAsAxiom
      [ axAnyDef ]
\end{code}

\section{Existential Conjectures}

$$
  \begin{array}{lll}
     \CJAnyRemove & \CJAnyRemoveS & \CJAnyRemoveN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyRemove = preddef ("exists" -.- "remove")
                      (exists [xs] p  ===  p)
                      ([xs] `notin` gvP)
\end{code}

$$
  \begin{array}{lll}
     \CJAnyFalse & & \CJAnyFalseN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyFalse = preddef ("exists" -.- "false")
                    (exists [xs] falseP  ===  falseP)
                    scTrue
\end{code}

$$\begin{array}{lll}
   \CJAnyOnePoint  & \CJAnyOnePointS  & \CJAnyOnePointN
\end{array}$$\par\vspace{-8pt}
\begin{code}
cjAnyOne = preddef ("exists" -.- "one" -.- "point")
  ( (exists [xs,ys] ((lvxs `areEqualTo` lves) /\ p) )
    ===
    (exists [ys] (Sub pred1 p (fromJust $ substn [] [(lvxs,lves)])) ) )
  ([xs] `notin` gves)
\end{code}

$$
  \begin{array}{lll}
  \\ \CJanyODistr & & \CJanyODistrN
  \end{array}
$$\par\vspace{-4pt}
\begin{code}
cjAnyOrDistr = preddef ("exists" -.- "or" -.- "distr")
  ( (exists [xs] (p \/ q)) === (exists [xs] p) \/ (exists [xs] q) )
  scTrue
\end{code}

$$
  \begin{array}{lll}
     \CJandAnyOScope & \CJandAnyOScopeS & \CJandAnyOScopeN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axAndAllScope = preddef ("and" -.- "exists" -.- "scope")
  ( p /\ (exists [xs,ys] q)
    === exists [xs] ( p /\ exists [ys] q) )
  ([xs] `notin` gvP)
\end{code}


$$
  \begin{array}{lll}
    \CJAnyOGen & & \CJAnyOGenN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyInst = preddef ("exists" -.- "gen")
  ( (exists [ys] (Sub pred1 p (fromJust $ substn [] [(lvxs,lves)])) )
    ==>
    (exists [xs,ys] p) )
  scTrue
\end{code}

\newpage
$$
  \begin{array}{lll}
     \CJAnyDummyRen  & \CJAnyDummyRenS  & \CJAnyDummyRenN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAnyDumRen = preddef ("exists" -.- "alpha" -.- "rename")
  ( (exists [xs] p)
    ===
    (exists [ys] (Sub pred1 p (fromJust $ substn [] [(lvxs,lvys)])) ) )
  ([ys] `notin` gvP)
\end{code}

$$
  \begin{array}{lll}
     \CJAnySwap &  \CJAnySwapN &
  \end{array}
$$
\vspace{-5pt}
\begin{code}
cjAnySwap = preddef ("exists" -.- "swap")
                    (exists [xs] (exists [ys] p)  
                     ===  
                     exists [ys] (exists [xs] p))
                    scTrue
\end{code}

$$
  \begin{array}{lll}
    \exists \lst x \bullet \exists \lst x \bullet P
    \equiv
    \exists \lst x \bullet P
    & \QNAME{$\exists$-idem}
  \end{array}
$$
\begin{code}
cjAnyIdem = preddef ("exists" -.- "idem")
                    (exists [xs] (exists [xs] p)  
                     ===  
                     (exists [xs] p))
                    scTrue
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

We now collect all of the rest above as conjectures:
\begin{code}
existsConjs :: [NmdAssertion]
existsConjs
  = [ cjAnyRemove, cjAnyFalse, cjAnyOne, cjAnyOrDistr
    , axAndAllScope, cjAnyInst, cjAnyDumRen, cjAnySwap, cjAnyIdem ]
\end{code}


\section{The Predicate Theory}

\begin{code}
existsName :: String
existsName = "Exists"
existsTheory :: Theory
existsTheory
  =  nullTheory { thName  =  existsName
            , thDeps  =  [ forallName
                         , equalityName
                         , implName
                         , aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , known   =  newNamedVarTable existsName
            , laws    =  predExistsAxioms
            , conjs   =  existsConjs
            }
\end{code}
