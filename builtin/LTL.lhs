\chapter{Linear Temporal Logic}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

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


\newpage
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

We use ``WVS.n'' to refer to axiom or theorem (n) 
from \cite{DBLP:journals/csur/WarfordVS20}.


\newpage
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
     \next (p \implies q) \equiv \next p \implies \next q 
     && \QNAME{$\next$-$\implies$-distr}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
axNextImpliesDistr 
  = preddef ("next" -.- "implies" -.- "distr")
            (mkN (p ==> q) ===  mkN p ==> mkN q)
            scTrue
\end{code}

$$
  \begin{array}{lll}
     \next p \equiv \lnot \next \lnot p &  & \QNAME{linearity}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
cjLinearity = ( "linearity"
              , (  mkN p === mkNot (mkN (mkNot p))
                , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     \next(p \lor q) \equiv \next p \lor \next q 
     && \QNAME{$\next$-$\lor$-distr}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
cjNextOrDistr = ( "next"-.-"or"-.-"distr"
        , (  mkN( p \/ q) === mkN p \/ mkN q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     \next(p \land q) \equiv \next p \land \next q 
     && \QNAME{$\next$-$\land$-distr}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
cjNextAndDistr = ( "next"-.-"and"-.-"distr"
        , (  mkN( p /\ q) === mkN p /\ mkN q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     \next(p \equiv q) \equiv \next p \equiv \next q 
     && \QNAME{$\next$-$\equiv$-distr}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
cjNextEqvDistr = ( "next"-.-"eqv"-.-"distr"
        , (  mkN( p === q) === (mkN p === mkN q)
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     \next \true \equiv \true && \QNAME{$\next$-$\true$}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
cjNextTrue = ( "next"-.-"true"
             , (  mkN trueP === trueP
               , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     \next \false \equiv \false && \QNAME{$\next$-$\false$}
  \end{array}
$$\par
\vspace{-8pt}
\begin{code}
cjNextFalse = ( "next"-.-"false"
        , (  mkN falseP === falseP
          , scTrue ) )
\end{code}

\newpage
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

$$
  \begin{array}{lll}
     \next (p \until q) \equiv \next p \until \next q 
     && \QNAME{$\next$-$\until$-distr}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axNextUntilDistr 
  = preddef ("next" -.- "U" -.- "distr")
            ( mkN (p `mkU` q) === (mkN p) `mkU` (mkN q) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     \next (p \until q) \equiv \next p \until \next q 
     && \QNAME{$\until$-def}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilDef
  = preddef ("U" -.- "def")
            ( (p `mkU` q) === q \/ (p /\ mkN (p `mkU` q)) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     (p \until \false) \equiv \false
     && \QNAME{$\until$-$\false$-r-zero}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilRZero
  = preddef ("U" -.- "false"-.-"r" -.- "zero")
            ( (p `mkU` falseP) === falseP )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     (p \until (q \lor r)) \equiv p \until q \lor p \until r
     && \QNAME{$\until$-$\lor$-l-distr}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilOrLDistr
  = preddef ("U" -.- "or" -.- "l" -.- "distr")
            ( (p `mkU` (q \/ r)) === (p `mkU` q) \/ (p `mkU` r) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     p \until r \lor q \until r \implies (p \lor q) \until r
     && \QNAME{$\until$-$\lor$-r-distr}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilOrRDistr
  = preddef ("U" -.- "or" -.- "r" -.- "distr")
            ( (p `mkU` r) \/ (q `mkU` r) ==> ((p \/ q) `mkU` r) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     (p \until (q \land r)) \implies p \until q \land p \until r
     && \QNAME{$\until$-$\land$-l-distr}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilAndLDistr
  = preddef ("U" -.- "and" -.- "l" -.- "distr")
            ( (p `mkU` (q /\ r)) ==> (p `mkU` q) /\ (p `mkU` r) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     ( p \until r \land q \until r \equiv (p \land q) \until r) )
     && \QNAME{$\until$-$\land$-r-distr}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilAndRDistr
  = preddef ("U" -.- "and" -.- "r" -.- "distr")
            ( (p `mkU` r) /\ (q `mkU` r) === ((p /\ q) `mkU` r) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
      p \until q \land \lnot q \until r \implies p \until r 
     && \QNAME{$\until$-$\implies$-ord}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilImplOrd
  = preddef ("U" -.- "impl" -.- "ord")
            ( (p `mkU` r) /\ (mkNot q `mkU` r) ==> (p `mkU` r) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
      p \until (q \until r) \implies (p \lor q) \until r 
     && \QNAME{$\until$-$\lor$-r-ord}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axUntilOrROrd
  = preddef ("U" -.- "or" -.- "r" -.- "ord")
            ( (p `mkU` (q `mkU` r)) ==> ((p \/ q) `mkU` r) )
            scTrue
\end{code}

$$
  \begin{array}{lll}
      p \until (q \land r) \implies (p \until q) \until r 
     && \QNAME{$\land$-$\until$-r-ord}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
axAndUntilROrd
  = preddef ("and" -.- "U" -.- "r" -.- "ord")
            ( p `mkU` (q /\ r) ==> (p `mkU` q) `mkU` r  )
            scTrue
\end{code}

$$
  \begin{array}{lll}
     (p \implies q) \until r 
     \implies
     (p \until r \implies q \until r) 
     && \QNAME{$\until$-$\implies$-r-distr}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilImpRDistr = ( "U"-.-"imp"-.-"r"-.-"distr"
        , (  ((p ==> q) `mkU` r) ==> (p `mkU` r ==> q `mkU` r)
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until \true \equiv \true
     && \QNAME{$\until$-$\true$-r-zero}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilTrueRZero = ( "U"-.-"true"-.-"r"-.-"zero"
        , (  p `mkU` trueP === trueP
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     \false \until q \equiv q
     && \QNAME{$\until$-l-unit}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilLUnit = ( "U"-.-"l"-.-"unit"
        , (  falseP `mkU` q === q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until p \equiv p
     && \QNAME{$\until$-idem}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilIdem = ( "U"-.-"idem"
        , (  p `mkU` p === p
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until q \lor  p \until \lnot q
     && \QNAME{$\until$-exc-mdl}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilExcMdl = ( "U"-.-"exc"-.-"mdl"
        , (  p `mkU` q \/ p `mkU` mkNot q
          , scTrue ) )
\end{code}

\newpage
$$
  \begin{array}{lll}
     \lnot p \until (q \until r) \land p \until r
     \implies
     q \until r 
     && \QNAME{WVS.24}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjWVS24 = ( "WVS.24"
        , ( (mkNot p `mkU` (q `mkU` r)) /\ p `mkU` q ==> q `mkU` r
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until (\lnot q \until r) \land q \until r
     \implies
     p \until r 
     && \QNAME{WVS.25}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjWVS25 = ( "WVS.25"
        , ( (p `mkU` (mkNot q `mkU` r)) /\ q `mkU` r ==> p `mkU` r
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until q \land \lnot q \until p \implies p 
     && \QNAME{WVS.26}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjWVS26 = ( "WVS.26"
        , ( (p `mkU` q) /\ (mkNot q `mkU` p) ==> p
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \land \lnot p \until q \implies q 
     && \QNAME{WVS.27}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjWVS27 = ( "WVS.27"
        , ( p /\ (mkNot p `mkU` q) ==> q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until q \implies p \lor q
     && \QNAME{WVS.28}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjWVS28 = ( "WVS.28"
        , ( p `mkU` q ==> p \/ q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     q \implies p \until q 
     && \QNAME{$\until$-insert}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilInsert = ( "U" -.- "insert"
        , ( q ==> p `mkU` q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \land q \implies p \until q 
     && \QNAME{WVS.30}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjWVS30 = ( "WVS.30"
        , ( p /\ q ==> p `mkU` q
          , scTrue ) )
\end{code}


$$
  \begin{array}{lll}
     p \lor p \until q \equiv p \lor q 
     && \QNAME{absorb-WVS.31}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilAbs31 = ( "absorb"-.-"WVS.31"
        , ( p \/ p `mkU` q === p \/ q
          , scTrue ) )
\end{code} 

$$
  \begin{array}{lll}
     p \until q \lor q \equiv p \until q 
     && \QNAME{absorb-WVS.32}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilAbs32 = ( "absorb"-.-"WVS.32"
        , ( p `mkU` q \/ q === p `mkU` q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until q \land q \equiv q
     && \QNAME{absorb-WVS.33}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilAbs33 = ( "absorb"-.-"WVS.33"
        , ( p `mkU` q /\ q === q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until q \lor (p \land q) \equiv p \until q 
     && \QNAME{absorb-WVS.34}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilAbs34 = ( "absorb"-.-"WVS.34"
        , ( p `mkU` q \/ (p /\ q) ===  p `mkU` q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until q \land (p \lor q) \equiv p \until q 
     && \QNAME{absorb-WVS.35}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilAbs35 = ( "absorb"-.-"WVS.35"
        , ( p `mkU` q /\ (p \/ q) === p `mkU` q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     p \until (p \until q) \equiv p \until q 
     && \QNAME{$U$-l-abs}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilLAbs = ( "U"-.-"l"-.-"abs"
        , ( p `mkU` (p `mkU` q) === p `mkU` q
          , scTrue ) )
\end{code}

$$
  \begin{array}{lll}
     (p \until q) \until q \equiv p \until q
     && \QNAME{$U$-r-abs}
  \end{array}
$$\par
\vspace{-4pt}
\begin{code}
cjUntilRAbs = ( "U"-.-"r"-.-"abs"
        , ( (p `mkU` q) `mkU` q === p `mkU` q
          , scTrue ) )
\end{code}

% $$
%   \begin{array}{lll}
%      law & sc & name
%   \end{array}
% $$\par
%\vspace{-4pt}
% \begin{code}
% axXXX 
%   = preddef ("law" -.- "name")
%             p
%             scTrue
% cjYYY = ( "conj"-.-"name"
%         , (  p
%           , scTrue ) )
% \end{code}

\newpage
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
            newNamedVarTable ltlName

\end{code}

\subsection{LTL Axioms}

We now collect all of the above as our axiom set:
\begin{code}
ltlAxioms :: [Law]
ltlAxioms
  = map labelAsAxiom
      [ axNextSelfDual, axNextImpliesDistr
      , axNextUntilDistr, axUntilDef, axUntilRZero
      , axUntilOrLDistr, axUntilOrRDistr, axUntilAndLDistr, axUntilAndRDistr
      , axUntilImplOrd, axUntilOrROrd, axAndUntilROrd
      ]
\end{code}

\subsection{LTL Conjectures}


We now collect our conjecture set:
\begin{code}
ltlConjs :: [NmdAssertion]
ltlConjs = map mkNmdAsn
    [ cjLinearity
    , cjNextOrDistr, cjNextAndDistr, cjNextEqvDistr, cjNextTrue, cjNextFalse
    , cjUntilImpRDistr, cjUntilTrueRZero, cjUntilLUnit
    , cjUntilIdem,cjUntilExcMdl
    , cjWVS24, cjWVS25, cjWVS26, cjWVS27, cjWVS28, cjUntilInsert, cjWVS30
    , cjUntilAbs31, cjUntilAbs32, cjUntilAbs33, cjUntilAbs34, cjUntilAbs35
    , cjUntilLAbs, cjUntilRAbs
    ]
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
