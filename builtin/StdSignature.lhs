\section{Standard Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module StdSignature (
  mkConsVar, mkConsIntro
, bool, boolf_1, boolf_2, boolf_3
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

Constructor names, if required to be known,
should be declared as known static predicate variable,
with a type that involves booleans.

\begin{code}
mkConsVar :: Identifier -> Variable
mkConsVar i = Vbl i PredV Static

mkConsIntro :: Identifier -> Type -> VarTable -> VarTable
mkConsIntro i t = fromJust . addKnownVar (mkConsVar i) t
\end{code}

\subsubsection{Propositional Variables}

\begin{code}
p = fromJust $ pVar $ Vbl (jId "P") PredV Static
q = fromJust $ pVar $ Vbl (jId "Q") PredV Static
r = fromJust $ pVar $ Vbl (jId "R") PredV Static
\end{code}

\subsubsection{Propositional Types}

\begin{code}
bool = GivenType $ jId $ "B"
boolf_1 = FunType bool bool
boolf_2 = FunType bool boolf_1
boolf_3 = FunType bool boolf_2
\end{code}

\subsubsection{Propositional Constants}

Now synonyms for the `theX` terms.
\begin{code}
trueP  =  theTrue -- Val P $ Boolean True
falseP =  theFalse -- Val P $ Boolean False
\end{code}

\newpage
\subsection{Propositional Operators}

\begin{code}
equiv = theEqv ; mkEquivs ps = PCons True equiv ps
mkEquiv p q = mkEquivs [p,q]
infix 1 === ; (===) = mkEquiv

implies = theImp ; mkImplies p q = PCons True implies [p,q]
infixr 2 ==> ; (==>) = mkImplies

lor = theOr
mkOrs []   =  falseP
mkOrs [p]  =  p
mkOrs ps   =  PCons True lor ps
mkOr p q   =  mkOrs [p,q]
infix 3 \/ ; (\/) = mkOr

land = theAnd
mkAnds []   =  trueP
mkAnds [p]  =  p
mkAnds ps   =  PCons True land ps
mkAnd p q = mkAnds [p,q]
infix 4 /\ ; (/\) = mkAnd

lnot = theNot ; mkNot p = PCons True lnot [p]

equals = jId "="
isEqualTo   e1  e2  = Cons P True           equals [ e1, e2]
areEqualTo es1 es2  = Iter P True land True equals [es1,es2]
\end{code}


\subsubsection{Propositional Law Shorthand}

All \emph{propositional} laws are characterised by not having
any side-conditions:
\begin{code}
propdef ( name, prop ) = ( name, fromJust $ mkAsn prop scTrue )
\end{code}

\subsection{Predicate Infrastructure}


\subsubsection{Predicate Constants}

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


\subsubsection{Predicate Law Shorthand}

General predicate laws often have side-conditions:
\begin{code}
preddef :: String -> Term -> SideCond -> NmdAssertion
preddef name pred sc = ( name, fromJust $ mkAsn pred sc )
\end{code}

\begin{code}
mkNmdAsn :: (String, (Term, SideCond)) -> NmdAssertion
mkNmdAsn (name, (pred, sc)) = (name, fromJust $ mkAsn pred sc)
\end{code}
