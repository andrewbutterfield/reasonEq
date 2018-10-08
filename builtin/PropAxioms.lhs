\section{Propositional Axioms}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropAxioms (
  bool
, true, trueP
, false, falseP
, equiv, mkEquiv, mkEquivs, (===)
, lnot, mkNot
, lor, mkOr, mkOrs, (\/)
, land, mkAnd, mkAnds, (/\)
, implies, mkImplies, (==>)
, propSignature
, propdef
, flattenEquiv
, propKnown
, propAxioms
, propAxiomName
, propAxiomTheory
) where

import Data.Maybe

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

\newpage
\subsection{Propositional Operators}

\begin{code}
equiv = fromJust $ ident _equiv ; mkEquivs ps = PCons equiv ps
mkEquiv p q = mkEquivs [p,q]
infix 1 === ; (===) = mkEquiv

implies = fromJust $ ident _implies ; mkImplies p q = PCons implies [p,q]
infixr 2 ==> ; (==>) = mkImplies

lor = fromJust $ ident _lor
mkOrs []   =  falseP
mkOrs [p]  =  p
mkOrs ps   =  PCons lor ps
mkOr p q   =  mkOrs [p,q]
infix 3 \/ ; (\/) = mkOr

land = fromJust $ ident _land
mkAnds []   =  trueP
mkAnds [p]  =  p
mkAnds ps   =  PCons land ps
mkAnd p q = mkAnds [p,q]
infix 4 /\ ; (/\) = mkAnd

lnot = fromJust $ ident _lnot ; mkNot p = PCons lnot [p]
\end{code}

\subsubsection{The Propositional Signature}
\begin{code}
propSignature = LogicSig trueP falseP equiv implies land
flattenEquiv = flattenTheEquiv propSignature
\end{code}

All propositional laws are characterised by not having
any side-conditions:
\begin{code}
propdef ( name, prop ) = ( name, ( prop, scTrue ) )
\end{code}


\subsection{Propositional Axioms}

\subsubsection{Known Variables}

These are precisely the two propositional constants,
with \textit{true} known as boolean,
and \textit{false} known as it's negation.
$$
  \begin{array}{ll}
     \AXtrue     & \AXtrueN
  \\ \AXfalseDef & \AXfalseDefN
  \end{array}
$$

\begin{code}
propKnown :: VarTable
propKnown   =  fromJust $ addKnownConst false (mkNot trueP) $
               fromJust $ addKnownVar true  bool newVarTable
axTrue      =  ( "true",      ( trueP,                  scTrue ) )
axFalseDef  =  ( "false-def", ( falseP === mkNot trueP, scTrue ) )
\end{code}

\newpage
\subsubsection{Axioms}

$$
  \begin{array}{ll}
     \AXeqvRefl & \AXeqvReflN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvRefl
 = ( _equiv++"_refl"
   , ( p === p
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXeqvAssoc & \AXeqvAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvAssoc
 = ( _equiv++"_assoc"
   , ( ((p === q) === r) === (p === (q === r))
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXeqvSymm & \AXeqvSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvSymm
 = ( _equiv++"_symm"
   , ( flattenEquiv ( (p === q) === (q === p) )
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXnotEqvDistr & \AXnotEqvDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axNotEqvDistr
 = ( _lnot++"_"++_equiv++"_distr"
   , ( mkNot(p === q) ===  ((mkNot p) === q)
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXorSymm & \AXorSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrSymm
 = ( _lor++"_symm"
   , ( p \/ q === q \/ p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorAssoc & \AXorAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrAssoc
 = ( _lor++"_assoc"
   , ( (p \/ q) \/ r === p \/ (q \/ r)
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorIdem & \AXorIdemN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrIdem
 = ( _lor++"_idem"
   , ( p \/ p === p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorEqvDistr & \AXorEqvDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrEqvDistr
 = ( _lor++"_"++_equiv++"_distr"
   , ( flattenEquiv ( (p \/ (q === r)) === (p \/ q === p \/ r) )
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXexclMdl & \AXexclMdlN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axExclMidl
 = ( "excl-middle"
   , ( p \/ mkNot p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXgoldRule & \AXgoldRuleN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axGoldRule
 = ( "golden-rule"
   , ( (p /\ q) === ((p === q) === p \/ q)
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXimplDef & \AXimplDefN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axImplDef
 = ( _implies++"_def"
   , ( flattenEquiv ( p ==> q === (p \/ q === q) )
   , scTrue ) )
\end{code}

We now collect all of the above as our axiom set:
\begin{code}
propAxioms :: [Law]
propAxioms
  = map labelAsAxiom
      [ axTrue, axEqvRefl, axEqvAssoc, axEqvSymm
      , axFalseDef, axNotEqvDistr
      , axOrSymm, axOrAssoc, axOrIdem, axOrEqvDistr, axExclMidl
      , axGoldRule, axImplDef ]
\end{code}


\subsection{The Propositional Theory}

\begin{code}
propAxiomName :: String
propAxiomName = "PropAxioms"
propAxiomTheory :: Theory
propAxiomTheory
  =  Theory { thName  =  propAxiomName
            , thDeps  =  []
            , known   =  propKnown
            , laws    =  propAxioms
            , proofs  =  []
            , conjs   =  []
            }
\end{code}
