\chapter{Standard Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module StdSignature (
  mkKnownVar, mkConsVar, mkConsIntro
, trueP
, falseP
, equiv, mkEquiv, mkEquivs, (===)
, lnot, mkNot
, lor, mkOr, mkOrs, (\/)
, land, mkAnd, mkAnds, (/\)
, implies, mkImplies, (==>)
, equals, isEqualTo, areEqualTo
, propdef
, flattenEquiv
, forall, exists, univ, sat
, preddef, mkNmdAsn
) where

import Data.Maybe
import qualified Data.Set as S

import Symbols

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
\end{code}


\newpage
\section{Introduction}

Here we present a hard-coded implementation of
propositional equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
However, we also make some key changes to the choice
of axioms.
In particular, we choose to have \textit{true}, and reflexivity
of $\equiv$ as axioms, and relegate $\CJeqvIdN$ to mere theorem-hood.
The reason for this is that the fundamental proof mechanism in both
Gries\&Schneider and Tourlakis is to reduce a conjecture to one of the axioms,
of which there are very many.
This is an expensive check to do after every proof step,
requiring matching against all the axioms.
Here, we require a proof to transform a conjecture to \textit{true},
which is more proof work%
\footnote{but not much!}%
, but is a much simpler, faster check.
We also omit axioms that define
inequivalence ($\not\equiv$) and consequence ($\impliedby$)
These will be introduced later via the definitional mechanism
(\texttt{VarData}).
$$
\AXPROP
$$
In this module we define the logical signature
we use, and supply some propositional infrastructure.
We do not define any theory here.
Instead we use modules to provide well-defined chunks
of axioms and theorems,
organised around key propositional operators.
In general we follow the presentation order of \cite{gries.93}:
\begin{description}
  \item [\texttt{Equivalence}]
    Laws for $true$ and $\equiv$, in the \texttt{Equiv} theory.
  \item [\texttt{Negation}]
    Laws for $false$ and $\lnot$, in the \texttt{Not} theory.
\end{description}



\section{Propositional Infrastructure}


We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
the $\Bool$ type,
the constants \textit{true} and \textit{false},
and the infix symbols $\equiv$, $\lnot$, $\lor$, $\land$ and $\implies$.
The propositional constants, along with key propositional operators
are also exported in a logical signature,
as they have significance for proof strategies.

Constructor names, if required to be known,
should be declared as known static observation variables.

\begin{code}
mkKnownVar :: Variable -> Type -> VarTable -> VarTable
mkKnownVar v t  = fromJust . addKnownVar v t

mkConsVar ::  Identifier -> Type -> Variable
mkConsVar i t = Vbl i ObsV Static

mkConsIntro :: Identifier -> Type -> VarTable -> VarTable
mkConsIntro i t = mkKnownVar (mkConsVar i t) t
\end{code}

\subsection{Propositional Variables}

\begin{code}
p = fromJust $ pVar ArbType $ Vbl (jId "P") PredV Static
q = fromJust $ pVar ArbType $ Vbl (jId "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (jId "R") PredV Static
\end{code}

\subsection{Propositional Types}


\subsection{Propositional Constants}

Now synonyms for the `theX` terms.
\begin{code}
trueP  =  theTrue -- Val arbpred $ Boolean True
falseP =  theFalse -- Val arbpred $ Boolean False
\end{code}

\newpage
\section{Propositional Operators}

\begin{code}
equiv = theEqv ; mkEquivs ps = Cons arbpred True equiv ps
mkEquiv p q = mkEquivs [p,q]
infix 1 === ; (===) = mkEquiv

implies = theImp ; mkImplies p q = Cons arbpred True implies [p,q]
infixr 2 ==> ; (==>) = mkImplies

lor = theOr
mkOrs []   =  falseP
mkOrs [p]  =  p
mkOrs ps   =  Cons arbpred True lor ps
mkOr p q   =  mkOrs [p,q]
infix 3 \/ ; (\/) = mkOr

land = theAnd
mkAnds []   =  trueP
mkAnds [p]  =  p
mkAnds ps   =  Cons arbpred True land ps
mkAnd p q = mkAnds [p,q]
infix 4 /\ ; (/\) = mkAnd

lnot = theNot ; mkNot p = Cons arbpred True lnot [p]

equals = jId "="
p1 = arbpred
isEqualTo   e1  e2  = Cons p1 True           equals [ e1, e2]
areEqualTo es1 es2  = Iter p1 True land True equals [es1,es2]
\end{code}


\subsection{Propositional Law Shorthand}

All \emph{propositional} laws are characterised by not having
any side-conditions:
\begin{code}
propdef ( name, prop ) = ( name, fromJust $ mkAsn prop scTrue )
\end{code}

\section{Predicate Infrastructure}


\subsection{Predicate Constants}

\begin{code}
forallId = jId "forall"
forall vl p = fromJust $ pBnd forallId (S.fromList vl) p

existsId = jId "exists"
exists vl p = fromJust $ pBnd existsId (S.fromList vl) p

univId = fromJust $ brktIdent "[" "]"
univ p = Cls univId p

satId = fromJust $ brktIdent "langle" "rangle"
sat p = Cls satId p
\end{code}


\subsection{Predicate Law Shorthand}

General predicate laws often have side-conditions:
\begin{code}
preddef :: String -> Term -> SideCond -> NmdAssertion
preddef name pred sc = ( name, fromJust $ mkAsn pred sc )
\end{code}

\begin{code}
mkNmdAsn :: (String, (Term, SideCond)) -> NmdAssertion
mkNmdAsn (name, (pred, sc)) = (name, fromJust $ mkAsn pred sc)
\end{code}
