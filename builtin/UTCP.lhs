\chapter{Unifying Theories of Concurrent Programming}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTCP (
  i_atom, atom
, i_cskip, cskip
, i_cseq, cseq
, i_cplus, cplus
, i_cpll, cpll
, i_cstar, cstar
, utcpConjs, utcpName, utcpTheory
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
import UTPSignature
import UTPBase
import Arithmetic
import Sets
import Lists
import TestRendering

import Debugger
\end{code}

\def\Atm#1{\langle#1\rangle}
\def\rr#1{r{\scriptstyle{#1}}}
\def\RR#1{R{\scriptstyle{#1}}}
\def\pll{\parallel}
\def\llawnamebr{\mbox{\raisebox{2pt}{${\scriptscriptstyle\langle\!\langle\cdot}$}}}
\def\rlawnamebr{\mbox{\raisebox{2pt}{${\scriptscriptstyle\cdot\rangle\!\rangle}$}}}
\def\mkelabel#1{\textsf{\llawnamebr{#1}\rlawnamebr}}
\def\elab#1#2{\mkelabel{#1}\label{#2}}
\def\elabel#1{\elab{#1}{#1}}
\def\ecite#1{\mkelabel{#1}}
\def\eref#1{\mkelabel{#1, p\pageref{#1}}}

\def\done{\mathbf{!}}
\def\DIV{\mathbf{div}}
\def\miracle{\mathsf{miracle}}
\def\lref#1{\mkelabel{#1}}

\def\inv#1{{#1}^{-1}}
\def\isbij{\mathsf{isbij}}
\def\mapof#1{\{{#1}\}}


\def\RLEQNS#1{
  {$$\begin{array}{rcl@{\quad}l}
    #1
  \end{array}$$}
}
\def\RLEQNSs#1{
  \begin{eqnarray*}
  #1
  \end{eqnarray*}
}

\def\MATH#1{{\color{red!40!blue}{#1}}}
\def\m#1{\ensuremath{\MATH{#1}}}
\def\COZ#1{{\color{green!30!black}{#1}}}
\def\START#1{\lefteqn{{\MATH{#1}}}}
\def\coz#1{\rule[-6pt]{0pt}{18pt}\mbox{{\COZ{``{#1}''}}}}
\def\MORE#1{\\&&\coz{#1}}
\def\EQ#1{\\&=&\coz{#1}}
\def\EQm#1{\\&=&\coz{$#1$}}
\def\EQV#1{\\&\equiv&\coz{#1}}
\def\EQVm#1{\\&\equiv&\coz{$#1$}}
\def\IMP#1{\\&\implies&\coz{#1}}
\def\IMPm#1{\\&\implies&\coz{$#1$}}
\def\RBY#1{\\&\sqsubseteq&\coz{#1}}
\def\RBYm#1{\\&\sqsubseteq&\coz{$#1$}}
\def\THIS#1{\\&&\MATH{#1}}
\def\OLD#1{{\underline{#1}}}
\def\NEW#1{{\color{red}{#1}}}
\def\qed{{\color{green!50!black}\blacksquare}}
\def\QED{\\&\qed}
\def\say#1{\mbox{#1}}


\section{Introduction}

Here we implement the rooted version of UTCP.
We present the syntax,
then the low-level semantics that defines basic building blocks.



\section{Syntax for UTCP and CKA}

\begin{eqnarray*}
   a &\in& \Atom
\\ C &::=& \Atm a \mid \cskip \mid C \cseq C \mid C+C \mid C \pll C \mid C^*
\end{eqnarray*}
\begin{code}
atom :: Term -> Term
i_atom  =  jId "atom"
atom a  =  Cons arbpred False i_atom [a]
atomIntro  =  mkConsIntro i_atom boolf_1

cskip :: Term
i_cskip  =  jId "cskip"
v_cskip  =  Vbl i_cskip PredV Static
g_cskip  =  StdVar v_cskip
cskip    =  jVar arbpred v_cskip 
cskipIntro  =  mkConsIntro i_cskip bool

cseq :: Term -> Term -> Term
i_cseq = jId "cseq"
cseq c d = Cons arbpred True i_cseq [c,d]
cseqIntro  =  mkConsIntro i_cseq boolf_2

cplus :: Term -> Term -> Term
i_cplus = jId "cplus"
cplus c d = Cons arbpred True i_cplus [c,d]
cplusIntro  =  mkConsIntro i_cplus boolf_2

cpll :: Term -> Term -> Term
i_cpll = jId "cpll"
cpll c d = Cons arbpred True i_cpll [c,d]
cpllIntro  =  mkConsIntro i_cpll boolf_2

cstar :: Term -> Term
i_cstar  =  jId "cstar"
cstar c  =  Cons arbpred True i_cstar [c]
cstarIntro  =  mkConsIntro i_cstar boolf_1
\end{code}

We want predicate variables $C$, $D$, $E$ and $F$:
\begin{code}
c = fromJust $ pVar ArbType $ Vbl (jId "C") PredV Static
d = fromJust $ pVar ArbType $ Vbl (jId "D") PredV Static
e = fromJust $ pVar ArbType $ Vbl (jId "E") PredV Static
f = fromJust $ pVar ArbType $ Vbl (jId "F") PredV Static
\end{code}

\section{Low-Level Semantics}

\textbf{
Seriously consider going back to $in$,$g$, and $out$.
Also, we may want $r'$ to denote the after-value of $r$,
with a healthiness conditions that asserts $r'=r$,
to give a homogeneous alphabet.
}


Root expressions: 
\RLEQNS{
   S &\defs& \setof{1,2} 
\\ \sigma,\varsigma &\defs& S^*
\\ R &::=& r\sigma | r\sigma\done
}
Given that root-expressions are always of the form $r\sigma[\done]$ 
where $r$ is the one and only variable called ``r'', 
we can represent them just by $\sigma[\done]$.
\begin{code}
rexpr :: [Integer] -> Bool -> Term
rexpr_t = GivenType $ jId "RE"
i_rexpr = jId "r"
rexpr branchnos done 
  = Cons rexpr_t True i_rexpr 
      $ ( map (Val ArbType . Integer) branchnos 
          ++ [Val ArbType $ Boolean done] )
\end{code}
We want to predefine some common roots (all those used in semantics)
\begin{code}
r   = rexpr []  False
r'  = rexpr []  True
r1  = rexpr [1] False
r1' = rexpr [1] True
r2  = rexpr [2] False
r2' = rexpr [2] True
rdemo :: Term
rdemo 
  = lenum [ r, r', r1, r1', r2, r2' ]
cjDemo = ( "r" -.- "demo", ( rdemo, scTrue ) )
\end{code}

Label-set handling:
\RLEQNS{
   A \ominus (B,C) &\defs& (A \setminus B) \cup C
\\ ls(\ell) &\defs& \ell \in ls
\\ ls(L) &\defs& L \subseteq ls
\\ ls(\B\ell) &\defs& \ell \notin ls
\\ ls(\B L) &\defs& L \cap ls = \emptyset
}

\newpage
\section{Alphabet}

\begin{eqnarray*}
   s, s' &:& \mathcal S
\\ ls, ls' &:& \mathcal P (R)
\\ r &:& R \qquad  \textbf{(also }r':R\textbf{ ?)}
\\ \lst O &=& \setof{s,ls}
\end{eqnarray*}
\begin{code}
is  = jId "s" 
vs = Vbl is ObsV Before
vs' = Vbl is ObsV After
state_t = GivenType $ jId "S"
obs_vs_Intro  = mkKnownVar vs state_t
obs_vs'_Intro = mkKnownVar vs' state_t
ils  = jId "ls" 
vls = Vbl ils ObsV Before
vls' = Vbl ils ObsV After
ls_t = power rexpr_t
obs_vls_Intro  = mkKnownVar vls ls_t
obs_vls'_Intro = mkKnownVar vls' ls_t
ir  = jId "r" 
vr =  Vbl ir ObsV Static
r_t = rexpr_t
obs_r_Intro  = mkKnownVar vr rexpr_t
o = jId "O"  ;  vO = PreVar o
obsIntro = fromJust . addKnownVarSet vO (S.fromList $ map StdVar [vs,vls])
\end{code}


\section{Standard UTP}
``Standard'' UTP Constructs, specialised for our alphabet,
and noting that these do \emph{not} mention $r$
\RLEQNS{
   \Skip &=& ls'=ls \land s'=s & \lref{defn-$\Skip$}
\\ P \cond c Q
   &\defs&
   c \land P \lor \lnot c \land Q & \lref{defn-cond}
\\ P ; Q
   &~\defs~&
   \exists s_m,ls_m \bullet P[s_m,ls_m/s',ls'] \land Q[s_m,ls_m/s,ls]
   \lref{defn-$;$}
\\ c * P
   &=&
   P ; c * P \cond c \Skip & \lref{unfold-loop}
}
Having defined $\lst O = \setof{s,ls}$, the above should all work.


\section{Healthiness}

General shorthand, and Label Exclusivity invariant ($LE$):
\RLEQNS{
  \{L_1|L_2|\dots|L_n\} 
  &\defs&
   \forall_{i,j \in 1\dots n}
    \bullet
    i \neq j \implies L_i \cap  L_j = \emptyset
\\&& \lref{short-disj-lbl}
\\ ~[L_1|L_2|\dots|L_n] 
   &\defs&
   \forall_{i,j \in 1\dots n}
    \bullet
    i \neq j \implies
     ( L_i \cap ls \neq \emptyset \implies L_j \cap ls = \emptyset ) 
\\&& \lref{short-lbl-exclusive}
\\ LE &~\defs~& [r|r!]  \qquad \lref{inv-label-excl}
\\ DL &~\defs & \{r|r\done\} \qquad \lref{disj-lbls}
}

\textbf{Also?}
\RLEQNS{
   \mathbf{SV}_x(C) &\defs& C \land x'=x
\\ \mathbf{SVL}(C) &\defs& \mathbf{SV}_r(C)
}


The wheels-within-wheels healthiness condition
insists that $r$ and $r!$ are never simultaneously in
the label-set $ls$,
and that our semantic predicates are closed under mumbling.
\RLEQNS{
   ii &~\defs~& s'=s & \lref{defn-$ii$}
\\ C^0 &\defs& \Skip  & \lref{defn-$C^i$-base}
\\ C^{n+1} &\defs& C ; C^n & \lref{defn-$C^i$-rec}
\\ \bigvee_{i \in \Nat} C^i
   &=& 
   \Skip \lor (C\seq\bigvee_{i \in \Nat} C^i)
   &\lref{mumble-closure}
\\ \W(C)
   &\defs&
   [r|r!] \land \bigvee_{i\in \Nat} C^i
   & \lref{defn-$\W$}
}


\section{UTCP Semantics}

\subsection{Atomic Actions}

\subsubsection{Basic Definitions}

\RLEQNS{
   X(E|a|R|N)
   &~\defs~&
   ls(E) \land [a] \land ls'=(ls\setminus R)\cup N & \lref{defn-$X$}
\\ A(E|a|N)
   &\defs&
   X(E|a|E|N) & \lref{defn-$A$}
}
\begin{code}
-- X(E|a|R|A)
xact :: Term -> Term -> Term -> Term -> Term
i_xact = jId "X"
xact e act r a = Cons arbpred False i_xact [e,act,r,a]
xactIntro = mkConsIntro i_xact bool
-- A(E|a|N)
i_aact = jId "A"
aact e act n = Cons arbpred False i_aact [e,act,n]
aactIntro = mkConsIntro i_aact bool
\end{code}

We need to define some variables ($E$, $a$, $R$, $N$)
\begin{code}
vE = jVar ls_t $ ExprVar (jId "E") Static
vR = jVar ls_t $ ExprVar (jId "R") Static
vN = jVar ls_t $ ExprVar (jId "N") Static
va = jpVar $ PredVar (jId "a") Static
tls = jVar ls_t vls
tls' = jVar ls_t vls'
-- X(E|a|R|N)
axXDef = ( "X" -.- "def"
         , ( (xact vE va vR vN)
             ===
             ((vE `subseteq` tls) /\ va) /\
             (tls' `isEqualTo` ((tls `sdiff` vR) `sunion` vN))
           , scTrue ) ) 
-- A(E|a|N)
axADef = ( "A" -.- "def"
         , ( (aact vE va vN) === (xact vE va vE vN)
           , scTrue ) )
cjAAlt = ( "A" -.- "alt"
         , ( (aact vE va vN)
             ===
             ((vE `subseteq` tls) /\ va) /\
             (tls' `isEqualTo` ((tls `sdiff` vE) `sunion` vN))
           , scTrue ) )
\end{code}

\newpage
\subsubsection{Atomic Action Composition}

The most important law we need is that regarding sequential composition
of $X$-actions:
\RLEQNS{
\\ \lefteqn{X(E_1|a|R_1|N_1) ; X(E_2|b|R_2,N_2)}
\\ &\equiv&
   E_2 \cap (R_1\sminus N_1) = \emptyset
  ~\land~
   X(E_1 \cup (E_2\sminus N_1)
       \mid a\seq b
       \mid R_1 \cup R_2
       \mid (N_1 \sminus R_2) \cup  N_2)
       & \lref{$X$-$X$-comp}
}
\begin{code}
vE1 = jVar ls_t $ StaticVar $ jId "E1"
vE2 = jVar ls_t $ StaticVar $ jId "E2"
vb = jpVar $ PredVar (jId "b") Static
vR1 = jVar ls_t $ StaticVar $ jId "R1"
vR2 = jVar ls_t $ StaticVar $ jId "R2"
vN1 = jVar ls_t $ StaticVar $ jId "N1"
vN2 = jVar ls_t $ StaticVar $ jId "N2"
cjXXComp = ( "X" -.- "X" -.- "comp"
           , ( mkSeq (xact vE1 va vR1 vN1) (xact vE2 vb vR1 vN1)
               ===
               (vE2 `sunion` (vR1 `sdiff` vN1) `isEqualTo` mtset)
               /\
               (xact 
                 (vE1 `sunion` (vE2 `sdiff` vN1)) 
                 (mkSeq va vb) 
                 (vR1 `sunion` vR2) 
                 ((vN1 `sdiff` vR2) `sunion` vN2) )
             , scTrue ))
\end{code}

\subsection{Commands}

(they lack sufficient invariants):
\RLEQNS{
   \Atm a &~\defs~&\W(A(r|a|r!)) & \lref{defn-$\Atm a$}
\\ \cskip &\defs& \Atm{ii} & \lref{defn-$\cskip$}
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|r1)
      \lor C[r1/r]
      \lor A(r1!|ii|r2)
      \lor D[r2/r]
      \lor A(r2!|ii|r!) ~) &\lref{defn-$\cseq$}
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|r1) \lor A(r|ii|r2) &\lref{defn-$+$}
\\ && \qquad {} \lor
   C[r1/r] \lor D[r2/r]
\\ && \qquad {} \lor A(r1!|ii|r!) \lor A(r2!|ii|r!) ~)
\\ C \pll D
   &\defs&
   \W(\quad\phlor A(r|ii|r1,r2) &\lref{defn-$\pll$}
\\ && \qquad {}\lor
   C[r1/r]
   \lor D[r2/r]
\\ && \qquad {}\lor
   A(r1!,r2!|ii|r!)~)
\\ C^*{} 
   &\defs&
   \W(\quad  \phlor A(r|ii|r1) \lor A(r1|ii|r!) &\lref{defn-$*$}
\\ && \qquad {}\lor C[r1/r]    \lor A(r1!|ii|r1) ~)
}

We note that $\cskip$ expands to:
$$
[r|r!] \land s'=s \land ( ls'=ls \lor ls' = (ls\sminus r)\cup r!)
$$
State $s$ is unchanged, and either $ls$ is unchanged (stutter),
or flow-control ``moves'' from $r$ to $r!$.

\section{Invariant Satisfaction}

We specify how $A$ and $X$ atomic actions 
should satisfy a label-based invariant $I$: 
\RLEQNS{
   A(E|a|N) \textbf{ sat } I
   &\defs&
   E \textbf{ lsat } I \land N \textbf{ lsat } I
   & \lref{defn-$A$-\textbf{sat}}
\\ X(E|a|R|A)  \textbf{ sat } I
   &\defs&
   E \textbf{ lsat } I \land A \textbf{ lsat } I
   & \lref{defn-$X$-\textbf{sat}}
\\ S \textbf{ lsat } [L_1|\dots|L_n]
   &\defs&
   \forall i,j,r \bullet 
      i=j \lor r \notin S \lor r \notin L_i \lor r \notin L_j
   & \lref{defn-\textbf{lsat}}
\\ I \textbf{ invTrims } X(E|a|E,L|A)
   &\defs&
   \lnot(\setof{E,L} \textbf{ lsat } I)
   & \lref{defn-\textbf{invTrims}}
}


\section{Laws of CKA}

\begin{mathpar}
e+0 = e \and e+e = e \and e+f = f+e \and e+(f+g) = (e+f)+g
\\
e;1 =e \and 1;e = e \and e;(f;g) = (e;f);g
\\
e;0 = 0 = 0;e \and e;(f+g) = e;f + e;g \and (e+f);g = e;g + f;g
\\
e \pll f = f \pll e \and e \pll 1 = e 
\and 
e \pll (f \pll g) = (e \pll f) \pll g
\\
e \pll 0 = 0 \and e \pll (f+g) = e \pll f + e \pll g
\\
1 + e;e^* = e^* \and e + f;g \leq g \implies f^*;e \leq g
\\
(e\pll f);(g\pll h) \leq (e;g)\pll (f;h)
\end{mathpar}


\section{The Theorems}

There are some clear mappings between the CKA and UTCP notations:
\begin{mathpar}
  1\mapsto \cskip 
  \and +\mapsto+ 
  \and ;\mapsto\cseq
  \and \pll\mapsto\pll
  \and *\mapsto *
\end{mathpar}
The miracle concept is not present in the Views paper,
and we defer consideration of it until we have worked through the known stuff.

Theorems to be proven, where ($C$,$D$,$E$,$F$, range over commands):
\RLEQNS{
   C+\miracle &=& C & \mkelabel{ndc-miracle-zero}
\\ C+C &=& C & \mkelabel{ndc-idem}
\\ C+D &=& D+C & \mkelabel{ndc-symm}
\\ C+(D+E) &=& (C+D)+E & \mkelabel{ndc-assoc}
\\ C\cseq\cskip &=&C & \mkelabel{seq-r-unit}
\\ \cskip\cseq C &=& C & \mkelabel{seq-l-unit}
\\ C\cseq (D\cseq E) &=& (C\cseq D)\cseq E & \mkelabel{seq-assoc}
\\ C\cseq\miracle &=& \miracle  & \mkelabel{seq-miracle-r-zero}
\\ \miracle\cseq C &=& \miracle& \mkelabel{seq-miracle-l-zero}
\\ C\cseq(D+E) &=& C\cseq D + C\cseq E & \mkelabel{seq-ndc-distr}
\\ (C+D)\cseq E &=& C\cseq E + D\cseq E& \mkelabel{ndc-seq-distr}
\\ C \pll D &=& D \pll C & \mkelabel{par-symm}
\\ C \pll \cskip &=& C & \mkelabel{par-unit}
\\ C \pll (D \pll E) &=& (C \pll D) \pll E & \mkelabel{par-assoc}
\\ C \pll \miracle &=& \miracle  & \mkelabel{par-miracle-zero}
\\ C \pll (D+E) &=& C \pll D + C \pll E& \mkelabel{par-ndc-distr}
\\ \cskip + C\cseq C^* &=& C^* & \mkelabel{iter-fold}
\\ C + D\cseq E \leq E &\implies& D^*\cseq C \leq E & \mkelabel{refine1}
\\ (C\pll D)\cseq(E\pll F) &\leq& (C\cseq E)\pll (D\cseq F)
    & \mkelabel{exchange}
}

\subsection{Proof Methodology}

For each CKA equation
we represent the two sides with appropriate UTCP terms,
expand those in full, 
and identify a bijection over the labels in the two terms.

Key concepts (in approx order of presentation):
\begin{itemize}
   \item The X-after-X law and 
     what it says about sequencing contiguous A-actions,
     and arbitrary code blocks denoted by command-valued variables 
     (e.g. $C$, $D$, etc.).
   \item ``flows''. 
     $\W(C)$ is $\bigvee(C^i)$ which computes all possible flows.
     \\Emphasise that we can read off flows based on root expressions.
   \item Bijections and why they are relevant
\end{itemize}

\subsection{Bijections}

Some bijection laws:
\RLEQNS{
   \beta &:& A \fun b
\\ \beta(x)=\beta(y) &~\equiv~& x=y & \isbij
\\ \inv\beta(\beta(x))  &=& x
\\ \beta(\inv\beta(y))  &=& y
\\ \isbij(\beta) &\equiv& \isbij(\beta^{-1})
\\ \isbij(\beta_1) \land \isbij(\beta_2)
   &\implies& 
   \isbij(\beta_1 \circ \beta_2)
}
Given bijective $\beta : A \fun B$, 
and $F_T : (\Set T \times \dots \times \Set T) \fun \Bool$,
where $F_T$ is constructed from standard set operations like union, intersection
and set difference, 
then we have:
\RLEQNS{
  F_A(A_1,\dots,A_n) 
  &~\equiv~& 
  F_B(\beta(A_1),\dots,\beta(A_n))
}

We define the \emph{kernel} of an bijection of type $A \fun A$ 
to be the mappings such that $\beta(x) \neq x$.


\subsection{Summary}

\begin{enumerate}
\item We calculate out the LHS + RHS
\item We re-arrange to get complete flow-paths
\item We identify the relevant bijection kernel
\end{enumerate}

Because the all the substitutions are sound and ground we can work ``inside''
the $\W$ healthiness condition.
Let $\gamma$ be a sound and ground substitution.
Then $\W(C)\gamma  =  \W(C\gamma)$.
This means we do not need to expand or evaluate $\W(C)$ here,
but just focus on $C\gamma$.

Also, with the role played by $\Skip$ we can say that:
\RLEQNS{
\lefteqn{\Skip;\W(C)}
\\&=& \Skip;\bigvee_{i \in \Nat} C^i
\\&=& \bigvee_{i \in \Nat} (\Skip;C^i)
\\&=& \bigvee_{i \in \Nat} C^i
\\&=& \bigvee_{i \in \Nat} (\Skip;C)^i
\\&=&\W(\Skip ;C)
}

\newpage
\section{UTCP Theory}

We collect our known variables:
\begin{code}
utcpKnown
 = atomIntro $
   cskipIntro $
   cseqIntro $
   cplusIntro $
   cpllIntro $
   cstarIntro $
   xactIntro $ 
   aactIntro $
   obsIntro $
   obs_vs_Intro $ obs_vs'_Intro $
   obs_vls_Intro $ obs_vls'_Intro $
   obs_r_Intro $
   newVarTable
\end{code}



We now collect our axiom set:
\begin{code}
utcpAxioms :: [Law]
utcpAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ axXDef, axADef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utcpConjs :: [NmdAssertion]
utcpConjs
  = map mkNmdAsn
      [ cjAAlt, cjXXComp
      , cjDemo
      ]
\end{code}



\begin{code}
utcpName :: String
utcpName = "UTCP"
utcpTheory :: Theory
utcpTheory
  =  nullTheory { thName  =  utcpName
            , thDeps  =  [ utpBaseName
                         , uCloseName
                         , existsName
                         , forallName
                         , equalityName
                         , implName
                         , aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName
                         ]
            , known   =  utcpKnown
            , laws    =  utcpAxioms
            , conjs   =  utcpConjs
            }
\end{code}


\section{Rough Work}



Consider $X(E_1|a|R_1|A_1) ; X(E_2|b|R_2,A_2)$,
noting that atomic actions $a$ and $b$ only affect $s$ and $s'$,
and that the $E_i$, $R_i$, and $N_i$ are sets of labels/roots,
and only effect $ls$ and $ls'$.
We know the above is equivalent to 
$$
  E_2 \cap (R_1\sminus A_1) = \emptyset
  ~\land~
   X(E_1 \cup (E_2\sminus A_1)
       \mid a\seq b
       \mid R_1 \cup R_2
       \mid (A_1 \sminus R_2) \cup  A_2)
$$

\noindent 
The key feature here is that the first $X$ only enables the second one if
$E_2 \cap (R_1\sminus A_1) = \emptyset$.
Now, consider a bijection $\beta$ over labels, applied to all label sets.
The truth value of 
$\beta(E_2) \cap (\beta(R_1)\sminus \beta(A_1)) = \beta(\emptyset)$
is not changed as a result of the bijections.
In effect a bijective label-mapping applied to all label-related terms does not affect
flow of control.

\noindent There are some subtleties:
for $C+(D+E)=(C+D)+E$ we get a bijection 
$\mapof{r1 \mapsto r11, r21 \mapsto r12, r22 \mapsto r2}$,
and note the following disjuncts:
\\ LHS: 
$\left\{\begin{array}{l}
  A(r|ii|r1) ..C.. A(r1!|ii|r!) 
\\ A(r|ii|r2) A(r2|ii|r21) ..D..  A(r21!|ii|r2!)
\\ A(r2|ii|r22) ..E.. A(r22!|ii|r2!) A(r2!|ii|r!)
\end{array}\right.
$
\\ RHS: 
$\left\{\begin{array}{l}
   A(r|ii|r1) A(r1|ii|r11) C A(r11!|ii|r1!)
\\            A(r1|ii|r12) D A(r12!|ii|r1!) A(r1!|ii|r!)
\\ A(r|ii|r2) E A(r2!|ii|r!)
\end{array}\right.
$

\noindent There isn't a one-to-one matching between $A(\dots)$ 
as far as control-flow goes.
What we have are the following ``flow-paths'' from $r$ to $r!$:
\\ LHS: 
$\left\{\begin{array}{l}
  A(r|ii|r1) ; C[r1/r] ; A(r1!|ii|r!) 
\\ A(r|ii|r2) ; A(r2|ii|r21) ; D[r21/r] ; A(r21!|ii|r2!) ; A(r2!|ii|r!)
\\ A(r|ii|r2) ; A(r2|ii|r22) ; E[r22/r] ; A(r22!|ii|r2!) ; A(r2!|ii|r!)
\end{array}\right.
$
\\ RHS: 
$\left\{\begin{array}{l}
   A(r|ii|r1) ; A(r1|ii|r11) ; C[r11/r] ; A(r11!|ii|r1!) ; A(r1!|ii|r!)
\\ A(r|ii|r1) ; A(r1|ii|r12) ; D[r12/r] ; A(r12!|ii|r1!) ; A(r1!|ii|r!)
\\ A(r|ii|r2) ; E[r2/r] ; A(r2!|ii|r!)
\end{array}\right.
$

Lemma: $A(r_a|ii|r_b) ; A(r_b|ii|r_c) = A(r_a|ii|r_c)$,
provided that $\setof{r_a|r_b|r_c}$ and $[r_a|r_b|r_c]$ are true.
More specifically, we need at least $[r_a|r_b]$ to recover the $A()$ form.

We also generalise: $A(r_a|a|r_b) ; A(r_b|b|r_c) = A(r_a|a;b|r_c)$

\noindent Proof, in which we interpret $r_x$ as label-set $\setof{x}$,
where $x$ is the label produced by generator $r_x$:
\RLEQNSs{
  && A(r_a|a|r_b) ; A(r_b|b|r_c)
\EQ{$A()$ is $X()$}
\\&& X(r_a|a|r_a|r_b) ; A(r_b|b|r_b|r_c)
\EQ{Defn. of $X()$}
\\&& r_a \subseteq ls \land a \land ls' = (ls \sminus r_a) \cup r_b
     ~~;~~
     r_b \subseteq ls \land b \land ls' = (ls \sminus r_b) \cup r_c
\EQ{Defn. of $;$}
\\&& \exists s_m,ls_m \bullet {}
\\&& \qquad
     (r_a \subseteq ls \land a \land ls' = (ls \sminus r_a) \cup r_b)
     [s_m,ls_m/s',ls']
     \land {}
\\&& \qquad 
     (r_b \subseteq ls \land b \land ls' = (ls \sminus r_b) \cup r_c)
     [s_m,ls_m/s,ls]
\EQ{Substitution}
\\&& \exists s_m,ls_m \bullet {}
\\&& \qquad
     r_a \subseteq ls \land a[s_m/s'] \land ls_m = (ls \sminus r_a) \cup r_b     
     \land {}
\\&& \qquad 
     r_b \subseteq ls_m \land b[s_m/s] \land ls' = (ls_m \sminus r_b) \cup r_c
\EQ{1pt-rule, $ls_m = (ls \sminus r_a)$}
\\&& \exists s_m \bullet {}
\\&& \qquad
     r_a \subseteq ls \land a[s_m/s']   \land {}
\\&& \qquad 
     r_b \subseteq ((ls \sminus r_a) \cup r_b) \land b[s_m/s] 
     \land 
     ls' = (((ls \sminus r_a) \cup r_b) \sminus r_b) \cup r_c
\EQ{Reduce $\exists s_m$ scope}
\\&& (\exists s_m \bullet a[s_m/s'] \land b[s_m/s]) \land {}
\\&& r_a \subseteq ls 
     \land
     r_b \subseteq ((ls \sminus r_a) \cup r_b) 
     \land 
     ls' = (((ls \sminus r_a) \cup r_b) \sminus r_b) \cup r_c
\EQ{$S \subseteq (S \cup T)$ }
\\&& (\exists s_m \bullet a[s_m/s'] \land b[s_m/s]) 
     \land 
     r_a \subseteq ls 
     \land
     ls' = ((ls \sminus r_a) \cup r_b \sminus r_b) \cup r_c
\EQ{$(S \cup T)\sminus T = S$, if $S \cap T = \emptyset$}
\MORE{$[r_a|r_b] \land r_A \subseteq ls$ means that $r_b$ not in $ls$}
\\&& (\exists s_m \bullet a[s_m/s'] \land b[s_m/s]) 
     \land 
     r_a \subseteq ls 
     \land
     ls' = (ls \sminus r_a) \cup r_c
\EQ{Existential says $a;b$ (exercise!)}
\\&& (a;b)
     \land 
     r_a \subseteq ls 
     \land
     ls' = (ls \sminus r_a) \cup r_c
\EQ{Defn. $A()$}
\\&& A(r_a|a;b|r_c)
}

If we have $\setof{r_a|r_b}$ but not $[r_a|r_b]$ then  
$X(r_a|ii|r_a \cup r_b|r_c)$.
If we don't even have $\setof{r_a|r_b}$, then we get
$X(r_a|ii|r_a\sminus r_b \cup r_b\sminus r_a|r_c)$.


\noindent Given the above Lemma,
and noting that all exclusivity invariants apply,
we can simplify the ``flow-paths'' to:
\\ LHS: 
$\left\{\begin{array}{l}
   A(r|ii|r1)  ; C[r1/r]  ; A(r1!|ii|r!) 
\\ A(r|ii|r21) ; D[r21/r] ; A(r21!|ii|r!)
\\ A(r|ii|r22) ; E[r22/r] ; A(r22!|ii|r!)
\end{array}\right.
$

\noindent The bijection: 
$\mapof{r1 \mapsto r11, r21 \mapsto r12, r22 \mapsto r2}$
\\ RHS: 
$\left\{\begin{array}{l}
   A(r|ii|r11) ; C[r11/r] ; A(r11!|ii|r!)
\\ A(r|ii|r12) ; D[r12/r] ; A(r12!|ii|r!)
\\ A(r|ii|r2)  ; E[r2/r]   ; A(r2!|ii|r!)
\end{array}\right.
$

\noindent Now the bijection is clear.

\newpage
For some proofs we want to show the following (for arbitrary $\sigma$):
$$
P(C) ~\defs~ 
\left( 
A(r|ii|r\sigma) ~;~ C[r\sigma/r] ~;~ A(r\sigma!|ii|r!) = C
\right)
$$
This looks like an induction over the structure of $C$

Base Case $P(\Atm a)$

\RLEQNS{
   \lefteqn{A(r|ii|r\sigma) ~;~ \Atm a[r\sigma/r] ~;~ A(r\sigma!|ii|r!)}
\EQ{Defn. $\Atm a$}
\\&& A(r|ii|r\sigma) ~;~ A(r|a|r!)[r\sigma/r] ~;~ A(r\sigma!|ii|r!)
\EQ{Substitution}
\\&& A(r|ii|r\sigma) ~;~ A(r\sigma|a|r\sigma!) ~;~ A(r\sigma!|ii|r!)
\EQ{$A();A()$ lemma}
\\&& A(r|ii;a|r\sigma!) ~;~ A(r\sigma!|ii|r!)
\EQ{$A();A()$ lemma}
\\&& A(r|ii;a;ii|r!)
\EQ{$ii$ is unit for $;$}
\\&& A(r|a|r!)
\EQ{Defn $\Atm{}$ backwards}
\\&& \Atm a
}


Inductive Case: $P(C) \land P(D) \implies P(C \cseq D)$

Assume (replacing $\sigma$ by $\varsigma$,$\omega$):
\RLEQNS{
  && A(r|ii|r\varsigma) ~;~ C[r\varsigma/r] ~;~ A(r\varsigma!|ii|r!) = C
\\&& A(r|ii|r\omega) ~;~ D[r\omega/r] ~;~ A(r\omega!|ii|r!) = D
}
Show: 
  $ A(r|ii|r\sigma) ~;~ (C \cseq D)[r\sigma/r] ~;~ A(r\sigma!|ii|r!) 
    = (C \cseq D)
 $

\RLEQNS{
\lefteqn{A(r|ii|r\sigma) ~;~ (C \cseq D)[r\sigma/r] ~;~ A(r\sigma!|ii|r!)}
\EQ{Defn. $\cseq$}
\\&& A(r|ii|r\sigma) ~;  
\\&& (A(r|ii|r1) \lor C[r1/r] \lor 
   A(r1!|ii|r2) \lor D[r2/r] \lor A(r2!|ii|r!))[r\sigma/r] ~
\\&& ;~ A(r\sigma!|ii|r!)
\EQ{Substitution}
\\&& A(r|ii|r\sigma) ~; 
\\&& (A(r\sigma|ii|r\sigma1) \lor
     C[r\sigma1/r] \lor 
     A(r\sigma1!|ii|r\sigma2) \lor 
     D[r\sigma2/r] \lor 
     A(r\sigma2!|ii|r\sigma!)) ~
\\&& ;~ A(r\sigma!|ii|r!)
\EQ{Assumptions  with $\varsigma$,$\omega$}
\\&& A(r|ii|r\sigma) ~; 
\\&& (A(r\sigma|ii|r\sigma1) \lor {}
\\&& (A(r|ii|r\varsigma) ~;~ C[r\varsigma/r] ~;~ A(r\varsigma!|ii|r!))[r\sigma1/r] \lor{}
\\&& A(r\sigma1!|ii|r\sigma2) \lor {}
\\&& (A(r|ii|r\omega) ~;~ D[r\omega/r] ~;~ A(r\omega!|ii|r!))[r\sigma2/r] \lor {}
\\&&  A(r\sigma2!|ii|r\sigma!)) ~
\\&& ;~ A(r\sigma!|ii|r!)
\EQ{Substitution}
\\&& A(r|ii|r\sigma) ~; 
\\&& (A(r\sigma|ii|r\sigma1) \lor {}
\\&& (A(r\sigma1|ii|r\sigma1\varsigma) 
      ~;~ C[r\sigma1\varsigma/r] 
      ~;~ A(r\sigma1\varsigma!|ii|r\sigma1!)) \lor{}
\\&& A(r\sigma1!|ii|r\sigma2) \lor {}
\\&& (A(r\sigma1|ii|r\sigma1\omega) 
      ~;~ D[r\sigma2\omega/r] ~;~ A(r\sigma2\omega!|ii|r\sigma2!)) \lor {}
\\&&  A(r\sigma2!|ii|r\sigma!)) ~
\\&& ;~ A(r\sigma!|ii|r!)
\\
\\
\\&& A(r|ii|r\sigma) ~; 
\\&& (A(r\sigma|ii|r\sigma1\varsigma) 
      ~;~ C[r\sigma1\varsigma/r] 
      ~;~ A(r\sigma1\varsigma!|ii|r\sigma1!)) \lor{}
\\&& A(r\sigma1!|ii|r\sigma2) \lor {}
\\&& (A(r\sigma1|ii|r\sigma1\omega) 
      ~;~ D[r\sigma2\omega/r] ~;~ A(r\sigma2\omega!|ii|r!)
}
The first sequence of $A()$s reduces to $A(r|ii|r\sigma1\varsigma)$.
The end sequence becomes $A(r\sigma2\omega|ii|r!)$.


What is clear is that verifying proposed flows involves explicit
expansion of $\W$ iterations. 
The above case ($C\cseq D$) reduces to a single flow
\\
$ 
A(r|ii|r\sigma) ; A(r\sigma|ii|r\sigma1) ; 
C[r\sigma1/r] ; A(r\sigma1!|ii|r\sigma2) ; D[r\sigma2/r] ; 
A(r\sigma2!|ii|r\sigma!) ; A(r\sigma!|ii|r!)
$
but we need a convincing demonstration of why/how to show this

\newpage
Inductive Cases: 
$P(C) \land P(D) 
 \implies P(C + D)  \land P(C \pll D) \land P(C^*)
$
\RLEQNS{
  C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|r1) \lor A(r|ii|r2) 
\\ && \qquad {} \lor
   C[r1/r] \lor D[r2/r]
\\ && \qquad {} \lor A(r1!|ii|r!) \lor A(r2!|ii|r!) ~)
\\ C \pll D
   &\defs&
   \W(\quad\phlor A(r|ii|r1,r2) 
\\ && \qquad {}\lor
   C[r1/r]
   \lor D[r2/r]
\\ && \qquad {}\lor
   A(r1!,r2!|ii|r!)~)
\\ C^*{} 
   &\defs&
   \W(\quad  \phlor A(r|ii|r1) \lor A(r1|ii|r!) 
\\ && \qquad {}\lor C[r1/r]    \lor A(r1!|ii|r1) ~)
}


\newpage
\subsection{The Proofs}


\subsubsection{Nondeterministic Choice is Idempotent}
\begin{eqnarray*}
  && C+C = C \qquad \mkelabel{ndc-idem}
\\\lefteqn{C+C}
\EQ{defn $+$, re-arrange}
\\&& A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor C[r2/r] \lor A(r2!|ii|\rr!)
\\&& \dots
\\\lefteqn{C}
\EQ{id. substitution}
\\&& C[r/r]
\end{eqnarray*}
This isn't a simple label bijection argument.


\subsubsection{Nondeterministic Choice is Symmetric/Abelian}
\begin{eqnarray*}
  && C+D = D+C \qquad \mkelabel{ndc-symm}
\\\lefteqn{C+D} 
\EQ{defn $+$, re-arrange}
\\&& A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor D[r2/r] \lor A(r2!|ii|r!)
\\\lefteqn{D+C}
\EQ{defn $+$, re-arrange}
\\&& A(r|ii|r1) \lor D[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor C[r2/r] \lor A(r2!|ii|r!)
\EQ{re-arrange}
\\&& A(r|ii|r2) \lor C[r2/r] \lor A(r2!|ii|r!)  \lor {}
\\&& A(r|ii|r1) \lor D[r1/r] \lor A(r1!|ii|r!)
\end{eqnarray*}

Here we already have our flow-paths,
so can immediately read off the bijection kernel:
$
\mapof{ r1 \mapsto r2, r2 \mapsto r1
}
$.

\subsubsection{Nondeterministic Choice is Associative}
\begin{eqnarray*}
&& C+D = D+C \qquad \mkelabel{ndc-symm}
\\\lefteqn{C+(D+E)}
\EQ{defn. $+$, re-arrange}
\\&& A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor (D+E)[r2/r] \lor A(r2!|ii|r!)
\EQ{defn. $+$, re-arrange}
\\&& A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor {} 
\\&& \left(
     \begin{array}{l}
        A(r|ii|r1) \lor D[r1/r] \lor A(r1!|ii|r!) \lor {}
     \\ A(r|ii|r2) \lor E[r2/r] \lor A(r2!|ii|r!)
     \end{array}
     \right)[r2/r] \lor {}
\\&& A(r2!|ii|r!)
\EQ{substitution}
\\&& A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor {}
\\&& A(r2|ii|r21) \lor D[r21/r] \lor A(r21!|ii|r2!) \lor {}
\\&& A(r2|ii|r22) \lor E[r22/r] \lor A(r22!|ii|r2!) \lor {}
\\&& A(r2!|ii|r!) \\
\\\lefteqn{(C+D)+E)}
\EQ{defn. $+$, re-arrange}
\\&& A(r|ii|r1) \lor (C+D)[r1/r] \lor A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor E[r2/r] \lor A(r2!|ii|r!)
\EQ{defn. $+$, re-arrange}
\\&& A(r|ii|r1) \lor {} 
\\&& \left(
     \begin{array}{l}
        A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!) \lor {}
     \\ A(r|ii|r2) \lor D[r2/r] \lor A(r2!|ii|r!)
     \end{array}
     \right)[r1/r] \lor {}
\\&& A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor E[r2/r] \lor A(r2!|ii|r!)
\EQ{substitution}
\\&& A(r|ii|r1) \lor {} 
\\&& A(r1|ii|r11) \lor C[r11/r] \lor A(r11!|ii|r1!) \lor {}
\\&& A(r1|ii|r12) \lor D[r12/r] \lor A(r12!|ii|r1!) \lor {}
\\&& A(r1!|ii|r!) \lor {}
\\&& A(r|ii|r2) \lor E[r2/r] \lor A(r2!|ii|r!)
\end{eqnarray*}
We have already done the flow-path analysis in the Methodology
section above, so all we do here is re-present the
Bijection Kernel:
$\mapof{r1 \mapsto r11, r21 \mapsto r12, r22 \mapsto r2}$.


\subsubsection{Skip is a right-unit for Sequential Composition}
\begin{eqnarray*}
&& C\cseq\cskip = C  \qquad \mkelabel{seq-r-unit}
\\\lefteqn{C\cseq\cskip}
\EQ{Defn. of $\cseq$}
\\&&  A(r|ii|r1)
      \lor C[r1/r]
      \lor A(r1!|ii|r2)
      \lor \cskip[r2/r]
      \lor A(r2!|ii|r!)
\EQ{Defn. of $\cskip$}
\\&&  A(r|ii|r1)
      \lor C[r1/r]
      \lor A(r1!|ii|r2)
      \lor \Atm{ii}[r2/r]
      \lor A(r2!|ii|r!)
\EQ{Defn. of $\Atm{}$}
\\&&  A(r|ii|r1)
      \lor C[r1/r]
      \lor A(r1!|ii|r2)
      \lor A(r|ii|r!)[r2/r]
      \lor A(r2!|ii|r!)
\EQ{substitution}
\\&&  A(r|ii|r1)
      \lor C[r1/r]
      \lor A(r1!|ii|r2)
      \lor A(r2|ii|r2!)
      \lor A(r2!|ii|r!)
\\\lefteqn{C}
\end{eqnarray*}
We have one flow-path:
$$
 A(r|ii|r1) ~;~ C[r1/r] ~;~ A(r1!|ii|r2) ~;~ A(r2|ii|r2!) ~;~ A(r2!|ii|r!)
$$
which reduces to:
$$
 A(r|ii|r1) ~;~ C[r1/r] ~;~ A(r1!|ii|r!)
$$

Need new lemmas  about $\Atm{ii}$ as a unit for $;$.


\subsubsection{To be done}

\subsubsection{Property Statement}
\begin{eqnarray*}
&& property \qquad \mkelabel{prop-lbl}
\\\lefteqn{lhs}
\EQ{because}
\\\lefteqn{rhs}
\end{eqnarray*}

\RLEQNS{
   C\cseq\cskip &=&C & \mkelabel{seq-r-unit}
\\ \cskip\cseq C &=& C & \mkelabel{seq-l-unit}
\\ C\cseq (D\cseq E) &=& (C\cseq D)\cseq E & \mkelabel{seq-assoc}
\\ C\cseq(D+E) &=& C\cseq D + C\cseq E & \mkelabel{seq-ndc-distr}
\\ (C+D)\cseq E &=& C\cseq E + D\cseq E& \mkelabel{ndc-seq-distr}
\\ C \pll D &=& D \pll C & \mkelabel{par-symm}
\\ C \pll \cskip &=& C & \mkelabel{par-unit}
\\ C \pll (D \pll E) &=& (C \pll D) \pll E & \mkelabel{par-assoc}
\\ C \pll (D+E) &=& C \pll D + C \pll E& \mkelabel{par-ndc-distr}
\\ \cskip + C\cseq C^* &=& C^* & \mkelabel{iter-fold}
\\ C + D\cseq E \leq E &\implies& D^*\cseq C \leq E & \mkelabel{refine1}
\\ (C\pll D)\cseq(E\pll F) &\leq& (C\cseq E)\pll (D\cseq F)
    & \mkelabel{exchange}
}

\subsection{\protect$\miracle$}

MIRACLE LOOKS TRICKY


We need an equivalent for $0$, which satisfies:
\begin{mathpar}
    e+0=e \and e;0=0=0;e \and e\pll0=0
\end{mathpar}


We can define divergence: ($\DIV$).
\RLEQNS{
   \DIV &\defs& \W(\true) & \lref{defn-$\DIV$}
\\ &=& [r|r\done] \land \bigvee_{i\in \Nat} \true^i
\\ &=& [r|r\done] \land (\Skip \lor \true ; \bigvee_{i\in \Nat} \true^i )
\\ &=& [r|r\done] \land (\Skip \lor \true ; \bigvee_{i\in \Nat} \true )
\\ &=& [r|r\done] \land (\Skip \lor \true ; \true )
\\ &=& [r|r\done] \land (\Skip \lor \true )
\\ &=& [r|r\done] \land \true
\\ &=& [r|r\done]  & \lref{simp-$\DIV$}
}

We can define miracle?:
\RLEQNS{
   \miracle? &\defs& \W(\false) & \lref{defn-$\miracle$}
\\ &=& [r|r\done] \land \bigvee_{i\in \Nat} \false^i
\\ &=& [r|r\done] \land (\Skip \lor (\false ; \bigvee_{i\in \Nat} \false^i) )
\\ &=& [r|r\done] \land (\Skip \lor \false )
\\ &=& [r|r\done] \land \Skip 
\\ &=?& \cskip
}

Maybe miracle is simply $\false$? Then parallel can never terminate.


The miraculous stuff:
\RLEQNS{
   C+\miracle &=& C & \mkelabel{ndc-miracle-zero}
\\ C\cseq\miracle &=& \miracle  & \mkelabel{seq-miracle-r-zero}
\\ \miracle\cseq C &=& \miracle& \mkelabel{seq-miracle-l-zero}
\\ C \pll \miracle &=& \miracle  & \mkelabel{par-miracle-zero}
}

\RLEQNS{
 C+\miracle &=& C & \mkelabel{ndc-miracle-zero}
}
\begin{eqnarray*}
\lefteqn{C+\miracle}
\EQ{defn. of $+$.}
\\&& \W( A(r|ii|r1) \lor A(r|ii|r2)
         \lor C[r1/r] \lor \miracle[r2/r]
         \lor A(r1!|ii|r!) \lor A(r2!|ii|r!) ~)
\EQ{$\miracle=[r|r\done] \land ii$, substitution}
\\&& \W( A(r|ii|r1) \lor A(r|ii|r2)
         \lor C[r1/r] \lor ([r|r\done] \land ii)[r2/r]
         \lor A(r1!|ii|r!) \lor A(r2!|ii|r!) ~)
\EQ{substitution}
\\&& \W( A(r|ii|r1) \lor A(r|ii|r2)
         \lor C[r1/r] \lor ([r2|r2\done] \land ii)
         \lor A(r1!|ii|r!) \lor A(r2!|ii|r!) ~)
\EQ{\mkelabel{or-unit}, re-arrange}
\\&& \W( A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!)
\\&& \qquad \lor A(r|ii|r2) \lor ([r2|r2\done] \land ii) \lor A(r2!|ii|r!) ~)
\EQ{$[r2|r2\done]$ is true }
\\&& \W( A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!)
        \quad\lor\quad 
        A(r|ii|r2) \lor ii \lor A(r2!|ii|r!) ~)
\EQ{\lref{defn-$\W$}}
\\&& ~[r|r\done] \land 
      \bigvee_{i \in \Nat}( A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!)
                            \quad\lor\quad
                            A(r|ii|r2) \lor ii \lor A(r2!|ii|r!) ~)^i
\EQ{\lref{defn-$C^i$-base}, property of $\bigvee$}
\\&& ~[r|r\done] \land ( ii \lor 
      \bigvee_{i \in 1\dots}( A(r|ii|r1) \lor C[r1/r] \lor A(r1!|ii|r!)
         \lor A(r|ii|r2) \lor ii \lor A(r2!|ii|r!) ~)^i )
\end{eqnarray*}
Looks like we need the calculator!!!



















