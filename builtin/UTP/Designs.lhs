\chapter{UTP Designs}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.Designs (
  tok, tok' 
, i_design, design
, designName
, designTheory
) where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Substitution
import Theories

import StdTypeSignature
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
import UClose
import StdTypeSignature
import UTP.Reading
import UTP.While.RefineSig
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we define the UTP concept of Designs,
along with the relevant observables, 
constructors,
healthiness conditions,
and related theorems.

\section{Observables}

We have two Design-specific observables\cite[Defn 3.0.1, p75]{UTP-book}:
$$ 
  ok, ok' : \Bool
$$

\begin{code}
ok = jId "ok"  ;  vok = PreVar ok ; vok' = PostVar ok
tok = jVar bool vok  ;  tok' = jVar bool vok'
\end{code}




\section{The Design Theory}


\subsection{Known Variables}

\begin{code}
designKnown :: VarTable
designKnown =  fromJust $ addKnownVar v_design boolf_2 
                        $ newNamedVarTable designName
\end{code}


\subsection{Design Axioms}

Given a pre-condition $P$ and post-condition $Q$ 
over an alphabet that does not mention $ok$ or $ok'$,
we define a constructor that produces a health predicate that does include them:
$$ P \design Q $$
\begin{code}
vP = Vbl (jId "P") PredV Static ; p = fromJust $ pVar ArbType vP ; gP = StdVar vP
vQ = Vbl (jId "Q") PredV Static ; q = fromJust $ pVar ArbType vQ ; gQ = StdVar vQ
design :: Term -> Term -> Term
i_design    =  jId "design"
v_design    =  Vbl i_design ObsV Static
design p q  =  Cons arbpred False i_design [p, q]
\end{code}

From: \cite[Defn 3.1.1, p76]{UTP-book}:
$$
  \begin{array}{lll}
     P \design Q ~\defs~ ok \land P \implies ok' \land Q &
     & \QNAME{$\design$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
designIntro = mkConsIntro i_design boolf_2
(axDsgDef,alDsgDef) = bookdef ("refines" -.- "def") "defd1.5p34"
                         (design p q === (tok /\ p ==> tok' /\ q))
                         scTrue
\end{code}


\begin{code}
designAxioms :: [Law]
designAxioms  =  map labelAsAxiom [ axDsgDef ]
\end{code}

\subsection{Design Conjectures}

For now we just list definitions and theorems in Chp 2.
Some regarding assignment and skip should end up in \h{UTP.While.Design}

From: \cite[Thm 3.1.2,p77]{UTP-book}:
$$
[(P_1 \design Q_1) \implies (P_2 \design Q_2)] 
~~\mathbf{iff}~~
[P_2 \implies P_1]
~~\mathbf{and}~~
[(P_2 \land Q_2)\implies Q_2]
$$

P77:
$$
 [(P \design Q) \equiv (P \design P \land Q)]
 ~~\text{and}~~
 [(P \design Q) \equiv (P \design P \implies Q)]
$$

$$
[(P \design Q) \equiv (P \design R)] 
~~\mathbf{iff}~~
[(P \land Q) \implies R]
~~\text{and}~~
[R \implies (P \implies Q)]
$$

From \cite[\textbf{L1},p78]{UTP-book}:
$$
  \true ; (P \design Q) = \true
$$

From \cite[\textbf{Def. 3.1.3},p78]{UTP-book}:
$$
x := e ~~\defs~~ (\true \design x'=e \land y'=y \dots z'=z)
$$
Also
$$
x := e ~~\defs~~ (\mathcal D e \design x'=e \land y'=y \dots z'=z)
$$
Also (p79)
$$
P \cond b Q ~~\defs~~ (\mathcal D b \implies (b \land P \lor \lnot b \land Q))
$$

From \cite[\textbf{L2},p79]{UTP-book}:
$$
 (v:=e;v:=f(v)) ~~=~~ (v:=f(e))
$$

From \cite[\textbf{L3},pp79]{UTP-book}:
$$
 v:=e;(P \cond{b(v)} Q) ~~=~~ (v:=e;P) \cond{b(e)} (v:=e;Q)
$$


From \cite[p79]{UTP-book}:
$$
  \Skip ~~\defs~~ (\true \design x'=x \land \dots \land z'=z)
$$


From \cite[\textbf{L4},p79]{UTP-book}:
$$
  \Skip ; ( P \design Q) = (P \design Q)
$$

From \cite[\textbf{Theorem 3.1.4},p79]{UTP-book}:
$$
\begin{array}{ll}
   (1) & (P_1\design Q_1)\ndc(P_2 \design Q) 
         = 
         (P_1 \land P_2 \design Q_1 \lor Q_2)
\\ (2) & (P_1\design Q_1)\cond{b}(P_2 \design Q)
         =
         (P_1 \cond{b} P_2 \design Q_1 \cond{b}r Q_2)
\\ (3) & (P_1\design Q_1);(P_2 \design Q)
         =
         ( \lnot(\lnot P_1;\true) \land \lnot(Q_1;\lnot Q_2
           \design 
           Q_1 ;Q_2 )
\end{array}
$$
% From \cite[\textbf{Xn},pNN]{UTP-book}:
% From \cite[\textbf{Xn},pNN]{UTP-book}:

Pulling them all together:
\begin{code}
designConjs :: [NmdAssertion]
designConjs
  = [ 
    ]
\end{code}


\begin{code}
designName :: String
designName = "Designs"
designTheory :: Theory
designTheory
  =  nullTheory { thName  =  designName
                , thDeps  =  [ aoiName
                            , conjName
                            , disjName
                            , notName
                            , equivName ]
                , known   =  designKnown
                , laws    =  designAxioms
                , conjs   =  designConjs
                }
\end{code}


