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
import UTP.Observations
import UTP.While.Common
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
designKnown =  mkKnownVar v_design boolf_2 $
               mkKnownVar vok bool $
               mkKnownVar vok' bool $
               newNamedVarTable designName
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
(axDsgDef,alDsgDef) 
  = bookdef ("design" -.- "def") "defd1.5p34"
            (design p q === (tok /\ p ==> tok' /\ q))
            scTrue
\end{code}


\begin{code}
designAxioms :: [Law]
designAxioms  =  map labelAsAxiom [ axDsgDef ]
\end{code}

\subsection{Design Conjectures}

For now we just list definitions and theorems in Chp 3.
Some regarding assignment and skip should end up in \h{UTP.While.Design}

\subsubsection{Design Foundations and Concepts}

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
  \begin{array}{lll}
     \true ; (P \design Q) = \true
     && \QNAME{design-$;$-lzero}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjDesignLZero 
  = preddef ("design" -.- ";" -.- "lzero")
            (mkSeq trueP (design p q) === trueP)
            ( areUTPDynObs [gP,gQ] 
              .: isUTPCond (StdVar vok)
              .: isUTPCond' (StdVar vok') )
\end{code}




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
         ( \lnot(\lnot P_1;\true) \land \lnot(Q_1;\lnot P_2)
           \design 
           Q_1 ;Q_2 )
\end{array}
$$


From \cite[\textbf{Thm. 3.1.5},p80]{UTP-book}:
$$
\begin{array}{ll}
   (1) & \bigsqcap_i(P_i \design Q_i) 
         = 
         (\bigwedge_i P_i) \design (\bigvee_i Q_i)
\\ (2) & \bigsqcup_i(P_i \design Q_i) 
         = 
         (\bigvee_i P_i) \design (\bigwedge_i (P_i \implies Q_i))
\end{array}
$$


From \cite[p80]{UTP-book}:
$$
\top_\Design ~~ \defs ~~ (\true \design \false) ~=~ \lnot ok
$$

From \cite[\textbf{Thm. 3.1.6},p81]{UTP-book}:
$$
\begin{array}{rl}
                & \mu(X,Y)\bullet(F(X,Y)\design G(X,Y)) = (P(Q)\design Q)
\\ \text{where} & P(Y) = \nu X \bullet F(X,Y)
\\   \text{and} & Q = \mu Y \bullet (P(Y)\implies G(P(Y),Y))
\end{array}
$$

From \cite[\textbf{Exc 3.1.7},p82]{UTP-book}:
$$
\begin{array}{ll}
   (1) & \text{Prove that } \top_\Design ; (P \design Q) = \top_\Design
\\ (2) & \text{Prove that } (x:=e);\true ~~=~~ \true;(x:=e) ~~=~~ \true
\end{array}
$$


\subsubsection{Healthiness Conditions}

From \cite[\textbf{Defn 3.2.1},p82]{UTP-book}:
$$
\begin{array}{ll}
   \H{H1} & R = (ok \implies R)
\\ \H{H2} & [R[false/ok']\implies R[true/ok']]
\\ \H{H3} & R = R ; \Skip
\\ \H{H4} & R ; \true = true
\end{array}
$$

From \cite[\textbf{Thm 3.2.2},p83]{UTP-book}:
A predicate is \H{H1} ~~\IFF~~ it satisfies left-zero and left-unit
$$
\true;R = R = \Skip ; R
$$

From \cite[\textbf{Thm 3.2.3},p83]{UTP-book}:
A predicate is \H{H1} and \H{H2}~~\IFF~~ it is a design.
$$
\H{H1} \land \H{H2} \equiv \text{isDesign}
$$

From \cite[\textbf{Thm 3.2.4},p84]{UTP-book}:
A design is \H{H3} if its assumption $P$ can be expressed as a condition $p$.
$$
(p\design Q) = (p\design Q);\Skip
$$
Being \H{H3} allows us to simplify Thm 3.1.4(3) to
$$
(p_1\design Q_1);(p_2 \design Q)
         =
         ( p_1 \land \lnot(Q_1;\lnot p_2)
           \design 
           Q_1 ;Q_2 )
$$

From \cite[\textbf{Thm 3.2.5},p85]{UTP-book}:

$P\design Q$ satisfies \H{H4} ~~\IFF~~ $[\exists ok',x',\dots,z'\bullet (P\design  Q)]$.



From \cite[\textbf{Exc. 3.2.6},p85]{UTP-book}:
$$
\begin{array}{ll}
   (1) & \text{prove } ~~;~~\ndc~~\cond{\_}\text{ preserve healthiness}
\\ (2) & \text{Given } b(v) \design Q(v,v') \text{ is predeterministic if}
\\     & \qquad [(b(v)\land Q(v,v_1)\land Q(v,v_2))\implies(v_1=v_2)]
\\     & \text{Prove } ~~;~~ \cond{\_} \text{ preserve predeterminism}
\\ (3) & b \text{ is stable if }  b = b \land ok
\\     & \text{Given healthy } R \text{ and stable } b
\\     & \text{Prove }  R \wp b \text{ is stable}
\\     & \text{Prove }  R \wp false 
\end{array}
$$

% From \cite[\textbf{Xn},pNN]{UTP-book}:
% $$
% \begin{array}{ll}
%    (1) & stuff
% \end{array}
% $$

% From \cite[\textbf{Xn},pNN]{UTP-book}:
% $$
% \begin{array}{ll}
%    (1) & stuff
% \end{array}
% $$



Pulling them all together:
\begin{code}
designConjs :: [NmdAssertion]
designConjs
  = [ cjDesignLZero
    ]
\end{code}


\begin{code}
designName :: String
designName = "Designs"
designTheory :: Theory
designTheory
  = nullTheory  { thName  =  designName
                , thDeps  = [ utpCW_Name
                            , aoiName
                            , conjName
                            , disjName
                            , notName
                            , equivName ]
                , known   =  designKnown
                , laws    =  designAxioms
                , conjs   =  designConjs
                }
\end{code}


