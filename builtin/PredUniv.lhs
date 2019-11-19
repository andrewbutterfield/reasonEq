\section{Universal Closure}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PredUniv (
  univ
, predUnivConjs, predUnivName, predUnivTheory
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

import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import PropImpl
import Equality
import PredAxioms
import PredExists
import TestRendering
\end{code}


\newpage
\subsection{Introduction}


Here we present a hard-coded implementation of
predicate equational reasoning,
as inspired by Gries \& Schneider\cite{gries.93},
Gries' notes from the 1996 Marktoberdorf Summer School\cite{gries.97},
Tourlakis \cite{journals/logcom/Tourlakis01},
and described in \cite{DBLP:conf/utp/Butterfield12}.
However we adopt here a formulation closer to that of Gries\&Schneider,
as the Tourlakis form has useful laws such as the one-point rules
derived from his axioms by meta-proofs
\emph{that use non-equational reasoning}.

Reference \cite{gries.97} has only recently come to our attention,
where $[\_]$ is defined,
 as the same thing as the temporal box operator ($\Box$)
 of the logic C \cite[Section 5.2, p113; Table 8, p114]{gries.97}.

The inference rules and axioms,
given that $\Diamond P = \lnot \Box(\lnot P)$,
  are:
\begin{eqnarray*}
   \vdash P ~~\longrightarrow~~ \vdash \Box P
   && \textbf{Necessitation}
\\ \Box P    ~~\implies~~   P
   && \textbf{$\Box$-Instantiation}
\\ \Box(P\implies Q) ~~\implies~~ (\Box P \implies \Box Q)
   && \textbf{Monotonicity}
\\ \Diamond P ~~\implies~~ \Box \Diamond P
   && \textbf{Necessarily Possible}
\\ \vdash P ~~\longrightarrow~~ \vdash P^v_Q
   && \textbf{Textual Substitution}
\end{eqnarray*}
where the first four belong to temporal logic S5,
and the fifth produces logic C.
Logic C is both sound and complete, while S5 is incomplete.

In our notation we have two meta-theorems (1st and 5th above),
\begin{eqnarray*}
   P \text{ a theorem} & \text{then} & [P] \text{ a theorem}
\\ P \text{ a theorem} & \text{then} & P[Q/v] \text{ a theorem,}
\end{eqnarray*}
a definition $\langle P \rangle = \lnot[\lnot P]$,
and three axioms (2nd through 4th above)
\begin{eqnarray*}
   ~[P] &implies& P
\\ ~[P\implies Q] &\implies& ([P] \implies [Q])
\\ \langle P \rangle &\implies& [\langle P \rangle].
\end{eqnarray*}

Here is the current axiomatisation:
$$
\AXUNIVCLOSE
$$
$$
\CJUNIVCLOSE
$$


\subsection{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$ and $Q$,
the constant  $[\_]$,
and a generic binder variable: $\lst x$.

\subsubsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
gvP = StdVar vP
p = fromJust $ pVar vP
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
\end{code}

\subsubsection{Predicate Constants}

\begin{code}
univId = fromJust $ brktIdent "[" "]"
univ p = Cls univId p
\end{code}

\subsubsection{Generic Variables}

\begin{code}
vx = Vbl (fromJust $ ident "x") ObsV Static ; x = StdVar vx
lvxs = LVbl vx [] [] ; xs = LstVar lvxs
\end{code}

\newpage
\subsection{Universal Axioms}

% \begin{array}{lll}
%    \AXUnivDef & \AXUnivDefS & \AXUnivDefN
% \\ \AXPEqDef  & \AXPEqDefS  & \AXPEqDefN
% \end{array}

$$
  \begin{array}{lll}
     \AXUnivDef & \AXUnivDefS & \AXUnivDefN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axUnivDef = preddef ("[]" -.- "def")
                    (univ p  === forall [xs] p)
                    ([xs] `exCover` gvP)
\end{code}

$$
  \begin{array}{lll}
     \AXPEqDef  & \AXPEqDefS  & \AXPEqDefN
  \end{array}
$$\par\vspace{-8pt}
This definition assumes that \texttt{p} and \texttt{q}
are predicates, or, if expressions, are boolean-valued.
\begin{code}
aPEqDef = preddef ("=" -.- "def")
                  ((p `isEqualTo` q) === univ (p === q))
                  scTrue
\end{code}

\textbf{How do we enforce this?
What is the interaction like with \texttt{Equality} laws
such as \QNAME{$=$-refl}, or \QNAME{$=$-trans}?}

\subsection{Universal Conjectures}

$$
  \begin{array}{lll}
     \CJUnivIdem & \CJUnivIdemS & \CJUnivIdemN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjUnivIdem = preddef ("[]" -.- "idem")
                     (univ (univ p) === univ p)
                     scTrue
\end{code}


$$
  \begin{array}{lll}
     \CJandUnivDistr & \CJandUnivDistrS & \CJandUnivDistrN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAndUnivDistr = preddef ("land" -.- "[]" -.- "distr")
                (univ p /\ univ q === univ (p /\ q))
                scTrue
\end{code}

$$
  \begin{array}{lll}
     \CJtrueUniv & \CJtrueUnivS & \CJtrueUnivN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjUnivTrue = preddef ("univ" -.- "true")
                     (univ trueP === trueP)
                     scTrue
\end{code}

$$
  \begin{array}{lll}
     \CJfalseUniv & \CJfalseUnivS & \CJfalseUnivN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjUnivFalse = preddef ("univ" -.- "False")
                      (univ falseP === falseP)
                      scTrue
\end{code}

$$
  \begin{array}{lll}
     \CJallUnivClosed & \CJallUnivClosedS & \CJallUnivClosedN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjUnivAllClosed = preddef ("univ" -.- "forall" -.- "closed")
                          ((forall [xs] $ univ p) === univ p)
                          scTrue
\end{code}

$$
  \begin{array}{lll}
     \CJanyUnivClosed & \CJanyUnivClosedS & \CJanyUnivClosedN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjUnivAnyClosed = preddef ("univ" -.- "exists" -.- "closed")
                          ((exists [xs] $ univ p) === univ p)
                          scTrue
\end{code}


% %% TEMPLATE
% $$
%   \begin{array}{lll}
%      law & sc & name
%   \end{array}
% $$\par\vspace{-8pt}
% \begin{code}
% cjXXX = preddef ("law" -.- "name")
%                 p
%                 scTrue
% \end{code}

We now collect our axiom set:
\begin{code}
predUnivAxioms :: [Law]
predUnivAxioms
  = map labelAsAxiom
      [ axUnivDef, aPEqDef ]
\end{code}


We now collect our conjecture set:
\begin{code}
predUnivConjs :: [NmdAssertion]
predUnivConjs
  = [ cjUnivIdem, cjAndUnivDistr
    , cjUnivTrue, cjUnivFalse
    , cjUnivAllClosed, cjUnivAnyClosed ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
predUnivName :: String
predUnivName = "PredUniv"
predUnivTheory :: Theory
predUnivTheory
  =  Theory { thName  =  predUnivName
            , thDeps  =  [ predExistsName
                         , predAxiomName
                         , equalityName
                         , propImplName
                         , aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , known   =  newVarTable
            , laws    =  predUnivAxioms
            , proofs  =  []
            , conjs   =  predUnivConjs
            }
\end{code}
