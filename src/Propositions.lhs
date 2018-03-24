\section{Propositional Calculus}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Propositions (
  bool
, true, trueP
, false, falseP
, equiv, mkEquiv, mkEquivs, (===)
, lnot, mkNot
, lor, mkOr, mkOrs, (\/)
, land, mkAnd, mkAnds, (/\)
, implies, mkImplies, (==>)
, propKnown
, propLaws
, propConjs
) where

import Data.Maybe

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData

-- import Test.HUnit
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)
\end{code}


\subsection{Introduction}

Here we present a hard-coded implementation of
propositional equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
$$
\AXPROP
$$

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
the $\Bool$ type,
the constants \textit{true} and \textit{false},
and the infix symbols $\equiv$, $\lnot$, $\lor$, $\land$ and $\implies$.
The propositional constants, along with the equivelance and implication operators
are also exported as they have significance for proof strategies.

\subsection{Predicate Variables}

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}

\subsubsection{Propositional Type}

\begin{code}
bool = GivenType $ fromJust $ ident $ _mathbb "B"
\end{code}

\subsection{Propositional Constants}

\begin{code}
true = Vbl (fromJust $ ident "true") PredV Static
trueP = fromJust $ pVar true
false = Vbl (fromJust $ ident "false") PredV Static
falseP = fromJust $ pVar false
\end{code}

\subsection{Known Variables}

These are precisely the two propositional constants.
\begin{code}
propKnown :: VarTable
propKnown
 = fromJust $ addKnownVar true  bool $
   fromJust $ addKnownVar false bool newVarTable
\end{code}

\subsection{Propositional Operators}

\begin{code}
equiv = fromJust $ ident _equiv ; mkEquivs ps = PCons equiv ps
mkEquiv p q = mkEquivs [p,q]
infix 1 === ; (===) = mkEquiv

lnot = fromJust $ ident _lnot ; mkNot p = PCons lnot [p]

lor = fromJust $ ident _lor
mkOrs []   =  falseP
mkOrs [p]  =  p
mkOrs ps   =  PCons lor ps
mkOr p q   =  mkOrs [p,q]
infix 2 \/ ; (\/) = mkOr

land = fromJust $ ident _land
mkAnds []   =  trueP
mkAnds [p]  =  p
mkAnds ps   =  PCons land ps
mkAnd p q = mkAnds [p,q]
infix 3 /\ ; (/\) = mkAnd

implies = fromJust $ ident _implies ; mkImplies p q = PCons implies [p,q]
infixr 4 ==> ; (==>) = mkImplies
\end{code}

\subsection{Propositional Axioms}

$$
  \begin{array}{ll}
     \AXeqvAssoc & \AXeqvAssocN
  \end{array}
$$
\begin{code}
axEqvAssoc
 = ( _equiv++" assoc"
   , ((p === q) === r) === (p === (q === r))
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXeqvSymm & \AXeqvSymmN
  \end{array}
$$
\begin{code}
axEqvSymm
 = ( _equiv++"-symm"
   , (p === q) === (q === p)
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXeqvId & \AXeqvIdN
  \end{array}
$$
\begin{code}
axEqvId
 = ( _equiv++"-id"
   , (trueP === q) === q
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXfalseDef &\AXfalseDefN
  \end{array}
$$
\begin{code}
axFalseDef
 = ( "false-def"
   , falseP === mkNot trueP
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXnotEqvDistr & \AXnotEqvDistrN
  \end{array}
$$
\begin{code}
axNotEqvDistr
 = ( _lnot++"-"++_equiv++"-distr"
   , mkNot(p === q) ===  (mkNot p === q)
   , scTrue )
\end{code}


$$
  \begin{array}{ll}
     \AXorSymm & \AXorSymmN
  \end{array}
$$
\begin{code}
axOrSymm
 = ( _lor++"-symm"
   , p \/ q === q \/ p
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXorAssoc & \AXorAssocN
  \end{array}
$$
\begin{code}
axOrAssoc
 = ( _lor++"-assoc"
   , (p \/ q) \/ r === p \/ (q \/ r)
   , scTrue )
\end{code}

\newpage
$$
  \begin{array}{ll}
     \AXorIdem & \AXorIdemN
  \end{array}
$$
\begin{code}
axOrIdem
 = ( _lor++"-idem"
   , p \/ p === p
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXorEqvDistr & \AXorEqvDistrN
  \end{array}
$$
\begin{code}
axOrEqvDistr
 = ( _lor++"_"++_equiv++"_distr"
   , (p \/ (q === r)) === (p \/ q === p \/ r)
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXexclMdl & \AXexclMdlN
  \end{array}
$$
\begin{code}
axExclMidl
 = ( "excl-middle"
   , p \/ mkNot p
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXgoldRule & \AXgoldRuleN
  \end{array}
$$
\begin{code}
axGoldRule
 = ( "golden-rule"
   , (p /\ q) === ((p === q) === p \/ q)
   , scTrue )
\end{code}

$$
  \begin{array}{ll}
     \AXimplDef & \AXimplDefN
  \end{array}
$$
\begin{code}
axImplDef
 = ( _implies++"_def"
   , p ==> q === (p \/ q === q)
   , scTrue )
\end{code}

\begin{code}
propLaws :: [(String,Term,SideCond)]
propLaws
 = [ axEqvAssoc, axEqvSymm, axEqvId
   , axFalseDef, axNotEqvDistr
   , axOrSymm, axOrAssoc, axOrIdem, axOrEqvDistr, axExclMidl
   , axGoldRule, axImplDef ]
\end{code}

\newpage
\subsection{Propositional Conjectures}

We also supply a starter pack of conjectures to be proven:
$$\begin{array}{ll}
  P = Q & \LNAME{whatever}
\end{array}$$
\begin{code}
propConjs :: [(String,Term,SideCond)]
propConjs = []
\end{code}
