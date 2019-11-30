\section{Standard Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module StdSignature (
  bool
, trueP
, falseP
, equiv, mkEquiv, mkEquivs, (===)
, lnot, mkNot
, lor, mkOr, mkOrs, (\/)
, land, mkAnd, mkAnds, (/\)
, implies, mkImplies, (==>)
, propSignature
, propdef
, flattenEquiv
, forall, exists, univ, sat
, preddef
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
import TestRendering
\end{code}


\newpage
\subsection{Introduction}

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



\subsection{Propositional Infrastructure}


We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
the $\Bool$ type,
the constants \textit{true} and \textit{false},
and the infix symbols $\equiv$, $\lnot$, $\lor$, $\land$ and $\implies$.
The propositional constants, along with key propositional operators
are also exported in a logical signature,
as they have significance for proof strategies.

\subsubsection{Propositional Variables}

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}

\subsubsection{Propositional Type}

\begin{code}
bool = GivenType $ fromJust $ ident $ "B"
\end{code}

\subsubsection{Propositional Constants}

\begin{code}
trueP  = Val P $ Boolean True
falseP = Val P $ Boolean False
\end{code}

\newpage
\subsection{Propositional Operators}

\begin{code}
equiv = fromJust $ ident "equiv" ; mkEquivs ps = PCons equiv ps
mkEquiv p q = mkEquivs [p,q]
infix 1 === ; (===) = mkEquiv

implies = fromJust $ ident "implies" ; mkImplies p q = PCons implies [p,q]
infixr 2 ==> ; (==>) = mkImplies

lor = fromJust $ ident "lor"
mkOrs []   =  falseP
mkOrs [p]  =  p
mkOrs ps   =  PCons lor ps
mkOr p q   =  mkOrs [p,q]
infix 3 \/ ; (\/) = mkOr

land = fromJust $ ident "land"
mkAnds []   =  trueP
mkAnds [p]  =  p
mkAnds ps   =  PCons land ps
mkAnd p q = mkAnds [p,q]
infix 4 /\ ; (/\) = mkAnd

lnot = fromJust $ ident "lnot" ; mkNot p = PCons lnot [p]
\end{code}

\subsubsection{The Propositional Signature}
\begin{code}
propSignature = LogicSig trueP falseP equiv implies land lor
flattenEquiv = flattenTheEquiv propSignature
\end{code}



\subsubsection{Propositional Law Shorthand}

All \emph{propositional} laws are characterised by not having
any side-conditions:
\begin{code}
propdef ( name, prop ) = ( name, ( prop, scTrue ) )
\end{code}


\subsection{Predicate Infrastructure}


\subsubsection{Predicate Constants}

\begin{code}
forallId = fromJust $ ident "forall"
forall vl p = fromJust $ pBind forallId (S.fromList vl) p

existsId = fromJust $ ident "exists"
exists vl p = fromJust $ pBind existsId (S.fromList vl) p

univId = fromJust $ brktIdent "[" "]"
univ p = Cls univId p

satId = fromJust $ brktIdent "langle" "rangle"
sat p = Cls satId p
\end{code}

General predicate laws often have side-conditions:
\begin{code}
preddef name prop sc = ( name, ( prop, sc ) )
\end{code}
