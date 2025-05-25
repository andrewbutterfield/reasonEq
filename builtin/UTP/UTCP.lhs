\chapter{Unifying Theories of Concurrent Programming}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.UTCP (
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
import Types
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
import UTP.While.RefineSig
import UTP.Observations
import UTP.While.Common
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

\subsection{Label Generator Expressions}

Terse generator expression syntax:
\RLEQNS{
   g \in GVar &\defs& \setof{g}\qquad  \text{The \emph{sole} generator variable}
\\ p \in GPostOp &::=&  {:} \mid 1 \mid 2
\\ G \in GExpr &::=& g \mid G_p
\\ L \in LExpr &::=& \ell_G
}
Given that generator-expressions are always of the form $g\rho$ 
where $\rho : \Seq{GPostOp}$
and $g$ is the one and only variable (called ``g''), 
we can represent them just by $\rho$.
Here these post-operators are represented as integers,
with zero representing ``:''.
\begin{code}
gexpr :: [Integer] -> Term
gexpr_t = GivenType $ jId "GE"
i_gexpr = jId "G"
gexpr gops 
  = Cons gexpr_t True i_gexpr 
      $ ( map (Val ArbType . Integer) gops )
lexpr_t = GivenType $ jId "LE"
\end{code}

\subsection{Label-Sets}

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
\\ ls, ls' &:& \mathcal P (LExpr)
\\ g &:&  GExpr         \qquad \textbf{(also }g':G\textbf{ ?)}
\\ in,out &:& LExpr  \qquad \textbf{(also }in',out':LExpr\textbf{ ?)}
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
ls_t = power lexpr_t
obs_vls_Intro  = mkKnownVar vls ls_t
obs_vls'_Intro = mkKnownVar vls' ls_t
ig  = jId "g" 
vg =  Vbl ig ObsV Static
g_t = gexpr_t
obs_g_Intro  = mkKnownVar vg gexpr_t
iin  = jId "in" 
vin =  Vbl iin ObsV Static
in_t = lexpr_t
obs_in_Intro  = mkKnownVar vin lexpr_t
iout  = jId "out" 
vout =  Vbl iout ObsV Static
out_t = lexpr_t
obs_out_Intro  = mkKnownVar vout lexpr_t
o = jId "O"  
vO  = PreVar o  ; lO  = LVbl vO [] []  ; gO  = LstVar lO
vO' = PostVar o ; lO' = LVbl vO' [] [] ; gO' = LstVar lO'
dynAlf = [gO,gO']
stAlf  = map StdVar [vin,vg,vout]
obsIntro = fromJust . addKnownVarList vO (map StdVar [vs,vls])
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
   & \lref{defn-$;$}
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

\subsection{Label-Set Membership Lemmas}

To do the X-composition proof we need some lemmas:

An atomic action $A(E|a|N)$ is enabled if $E$ is contained
in the global label-set ($ls(E)$)
and results in $E$ being removed from that set, and new labels
$N$ being added ($ls'=(ls\setminus E)\cup N$).
We need a way to reason about containment in such an $ls'$
in terns of $E$ and $N$, and to compute sequential compositions
of such forms, which will take the more general form $X(E|a|R|A)$.

We find we get assertions of the form $(F(ls))(E)$,
asserting that $E$ is a subset of $F(ls)$ where $F$ is a set-function
composed of named/enumerated sets and standard set-operations.
We want to transform it into $ls(G) \land P$ where $G$ and $P$
do not involve $ls$.

We present the laws, with proofs in ``classical'' set notation.

We use $N$ denote new labels added on, 
$R$ for labels being removed,
and $C$ for labels being mixed in.
We also use $E$ when defining $X$ and $A$.
\begin{code}
[iS,iN,iR,iC,iE] = map jId ["S","N","R","C","E"]
mkLblSetVar iS = Vbl iS ExprV Static
[vS,vN,vR,vC,vE] = map mkLblSetVar [iS,iN,iR,iC,iE]
mkLblSetVarTerm vS = jVar ls_t vS
[tS,tN,tR,tC,tE] = map mkLblSetVarTerm [vS,vN,vR,vC,vE]
\end{code}

\subsubsection{Union becomes Difference}

\RLEQNS{
   (ls \cup N)(S)      &=& ls(S\setminus N)
}
\begin{code}
lmLSunion = 
  ( "ls" -.- "union" -.- "N"
  , ( (tS `subseteq` (tls `sunion` tN))
      ===
      ((tS `sdiff` tN) `subseteq` tls)
    , scTrue ) )
\end{code}
\RLEQNS{
\lefteqn{S \subseteq (ls \cup N)}
\\&=& x \in S \implies x \in (ls \cup N) & \say{``set definitions''}
\\&=& x \in S \implies x \in ls \lor x \in N & \say{``defn $\cup$''}
\\&=& x \notin S \lor x \in ls \lor x \in N & \say{``defn $\implies$''}
\\&=& x \notin S \lor x \in N \lor x \in ls & \say{``rearrange''}
\\&=& (x \in S \land x \notin N) \implies x \in ls 
    & \say{``De-Morgan, defn $\implies$''}
\\&=& (S \setminus N) \subseteq ls & \say{``defn $\subseteq$''}
}

\subsubsection{Difference becomes Conditional Intersection}

\RLEQNS{
   (ls \setminus R)(S) &=& ls(S) \land S \cap R = \emptyset
}
\RLEQNS{
\lefteqn{S \subseteq (ls \setminus R)}
\\&& x \in S \implies x \in (ls \setminus R)
 & \say{``set definitions''}
\\&& x \in S \implies x \in ls \land x \notin R
 & \say{``set definition''}
\\&& x \notin S \lor x \in ls \land x \notin R
 & \say{``defn $\implies$''}
\\&& (x \notin S \lor x \in ls)
     \land
     ( x \notin S \lor x \notin R)
 & \say{``distribution''}
\\&& (x \in S \implies x \in ls)
     \land
     \lnot( x \in S \land x \in R)
 & \say{``defn $\implies$, de-morgan''}
\\&&S \subseteq ls \land S \cap R = \emptyset
 & \say{``defn $\subseteq$''}
}

\subsubsection{Intersection becomes Conditional}

\RLEQNS{
  (ls \cap C)(S)      &=& ls(S) \land S \subseteq C
}
\RLEQNS{
\lefteqn{S \subseteq (ls \cap C)}
\\&& x \in S \implies x \in ls \land x \in C
 & \say{``set definitions''}
\\&& x \notin S \lor x \in ls \land x \in C
 & \say{``defn $\implies$''}
\\&& (x \notin S \lor x \in ls)
     \land
     (x \notin S \lor x \in C)
 & \say{``distribution''}
\\&& (x \in S \implies x \in ls)
     \land
     (x \in S \implies x \in C)
 & \say{``defn $\implies$''}
\\&& S \subseteq ls \land S \subseteq C
 & \say{``def $\subseteq$''}
}

\subsubsection{Difference then Union becomes Conditional Intersection of Difference}

\RLEQNS{
  ((ls \setminus R) \cup N)(S)
   &=& ls(S \setminus N) \land (S \setminus N) \cap R = \emptyset
}
\RLEQNS{
\lefteqn{((ls \setminus R) \cup N)(S)}
\\&& (ls \setminus R)(S \setminus N)
 & \say{``laws above''}
\\&& ls(S \setminus N) \land (S \setminus N) \cap R = \emptyset
 & \say{``laws above''}
}

\subsubsection{Difference then Union Twice is Complicated}

\RLEQNS{
\\ (((ls\setminus R_1) \cup N_1)\setminus R_2) \cup N_2
  &=& (ls \setminus (R_1 \cup R_2)) \cup ((N_1\setminus R_2) \cup N_2)
}

We note the following:
\RLEQNS{
\lefteqn{x \in (ls\setminus R_1) \cup N_1}
\\&& x \in (ls\setminus R_1) \lor x \in  N_1
 & \say{``defn $\cup$''}
\\&& x \in ls \land x \notin R_1 \lor x \in  N_1
 & \say{``defn $\setminus$''}
}
Then proceed:
\RLEQNS{
\lefteqn{x \in (((ls\setminus R_1) \cup N_1)\setminus R_2) \cup N_2}
\\&& x \in (ls\setminus R_1) \cup N_1) \land x \notin R_2 \lor x \in  N_2
 & \say{``above law''}
\\&& (x \in ls \land x \notin R_1 \lor x \in  N_1) \land x \notin R_2 \lor x \in  N_2
 & \say{``above law''}
\\&& (x \in ls \land x \notin R_1 \land x \notin R_2)
     \lor
     (x \in  N_1 \land x \notin R_2)
     \lor x \in  N_2
 & \say{``distributivity''}
\\&& (x \in ls \land \lnot(x \in R_1 \lor x \in R_2))
     \lor
     x \in  N_1 \setminus R_2
     \lor x \in  N_2
 & \say{``de-Morgan, defn $\setminus$''}
\\&& (x \in ls \land \lnot(x \in R_1 \cup R_2))
     \lor
     x \in  N_1 \setminus R_2 \cup  N_2
 & \say{``defn $\cup$, twice''}
\\&& (x \in ls \land x \notin R_1 \cup R_2)
     \lor
     x \in  N_1 \setminus R_2 \cup  N_2
 & \say{``tweak''}
\\&& x \in (ls \setminus R_1 \cup R_2)
     \lor
     x \in  N_1 \setminus R_2 \cup  N_2
 & \say{``definition of $\setminus$''}
\\&& x \in (ls \setminus R_1 \cup R_2)
     \cup
     (N_1 \setminus R_2 \cup  N_2)
 & \say{``definition of $\cup$''}
}


\subsection{Atomic Actions}

\subsubsection{Basic Definitions}

We know that $\lst O = \setof{s,ls}$, and similarly  for $\lst O'$,
but we also need to assert that $\setof{E,N,R} \disj \setof{\lst O,\lst O'}$.
\textbf{Note:}
\textsl{
  We don't need to assert $E \disj \lst O$,
  as we shuld be able to deduce this from the facts
  that $E$ is a term-variable and $\lst O$ denotes a set of obs-variables.
}
We need to define some variables ($E$, $a$, $R$, $N$)
\begin{code}
gE = StdVar vE
gN = StdVar vN
va = Vbl (jId "a") PredV Static ; a = fromJust $ pVar ArbType va 
tls = jVar ls_t vls
tls' = jVar ls_t vls'
eNotObs = [gO,gO'] `notin` gE
nNotObs = [gO,gO'] `notin` gN
eNO = [gE] `notin` gO  -- but this is really gE notin fv(gO), gO is listvar
nNO = [gN] `notin` gO  -- but this is really gN notin fv(gO), gO is listvar
\end{code}
We also need the fact that the alphabet of $a$ is limited
to $\setof{s,s'}$:
\begin{code}
isUTCPAtomic  :: GenVar -> SideCond
isUTCPAtomic  gc  = [StdVar vs,StdVar vs'] `dyncover` gc
areUTCPAtomic :: [GenVar] -> SideCond
areUTCPAtomic gcs = mrgscs $ map isUTCPAtomic gcs
\end{code}

\subsubsection{Extended Atomic Actions}

\RLEQNS{
   X(E|a|R|N)
   ~\defs~
   ls(E) \land a \land ls'=(ls\setminus R)\cup N 
   & \setof{E,N,R} \disj \setof{\lst O,\lst O'}
     ;
     \setof{s,s'} \supseteq_a \setof{a}
   & \lref{defn-$X$}
}
\begin{code}
xact :: Term -> Term -> Term -> Term -> Term
i_xact = jId "X"
xact e act r a = Cons arbpred False i_xact [e,act,r,a]
xactIntro = mkConsIntro i_xact bool
xactSC = isUTCPAtomic  (StdVar va) .: areUTPStcObs (map StdVar [vE,vR,vN])
axXDef = ( "X" -.- "def"
         , ( (xact tE a tR tN)
             ===
             ((tE `subseteq` tls) /\ a) /\
             (tls' `isEqualTo` ((tls `sdiff` tR) `sunion` tN))
           , xactSC ) )
\end{code}

We note that the following is true: \m{X(E|a|R|N) = X(E|a|(R\setminus N)|N)}.

\subsubsection{``Regular'' Atomic Actions}

\RLEQNS{
   A(E|a|N)
   ~\defs~
   X(E|a|E|N) 
   & \setof{E,N} \disj \setof{\lst O,\lst O'}
     ;
     \setof{s,s'} \supseteq_a \setof{a}
   & \lref{defn-$A$}
}
\begin{code}
i_aact = jId "A"
aact e act n = Cons arbpred False i_aact [e,act,n]
aactIntro = mkConsIntro i_aact bool
aactSC = isUTCPAtomic  (StdVar va) .: areUTPStcObs (map StdVar [vE,vN] )
axADef = ( "A" -.- "def"
         , ( (aact tE a tN) === (xact tE a tE tN)
           , aactSC ) )
cjAAlt = ( "A" -.- "alt"
         , ( (aact tE a tN)
             ===
             ((tE `subseteq` tls) /\ a) /\
             (tls' `isEqualTo` ((tls `sdiff` tE) `sunion` tN))
           , aactSC ) ) 
\end{code}

We note that \m{A(E_1|a|N_1) ; A(E_2|a|N_2)}
is \m{X(E_1|a|E_1|N_1) ; X(E_2|a|E_2|N_2)}
which expands to
$$
E_2 \cap (E_1\sminus N_1) = \emptyset
\land
X(E_1 \cup (E_2\sminus N_1)
       \mid a\seq b
       \mid E_1 \cup E_2
       \mid (N_1 \sminus E_2) \cup  N_2)
$$
(see conjecture below)
Noting that \m{E_i \disj N_i} this collapses to:
$$
E_2 \cap E_1  = \emptyset
\land
X(E_1 \cup (E_2\sminus N_1)
       \mid a\seq b
       \mid E_1 \cup E_2
       \mid (N_1 \sminus E_2) \cup  N_2)
$$




\newpage
\subsubsection{eXtended Atomic Action Composition}

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
\\ && \lst O,\lst O' \supseteq_a a,b
      \qquad
      \lst O,\lst O' \disj E_1,R_1,N_1,E_2,R_2,N_2
}
\begin{code}
vb = Vbl (jId "b") PredV Static ; b = fromJust $ pVar ArbType vb
vE1 = ExprVar (jId "E1") Static ; sE1 = jVar ls_t vE1
vE2 = ExprVar (jId "E2") Static ; sE2 = jVar ls_t vE2
vR1 = ExprVar (jId "R1") Static ; sR1 = jVar ls_t vR1
vR2 = ExprVar (jId "R2") Static ; sR2 = jVar ls_t vR2
vN1 = ExprVar (jId "N1") Static ; sN1 = jVar ls_t vN1
vN2 = ExprVar (jId "N2") Static ; sN2 = jVar ls_t vN2
cjXXComp = ( "X" -.- "X" -.- "comp"
           , ( mkSeq (xact sE1 a sR1 sN1) (xact sE2 b sR2 sN2)
               ===
               (sE2 `sintsct` (sR1 `sdiff` sN1) `isEqualTo` mtset)
               /\
               (xact 
                 (sE1 `sunion` (sE2 `sdiff` sN1)) 
                 (mkSeq a b) 
                 (sR1 `sunion` sR2) 
                 ((sN1 `sdiff` sR2) `sunion` sN2) )
             ,    areUTCPAtomic (map StdVar [va])
               .: areUTCPAtomic (map StdVar [vb])
               .: areUTPStcObs  (map StdVar [vE1,vE2,vR1,vR2,vN1,vN2]) 
               ) )
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
     \\Emphasise that we can read off flows based on generator expressions.
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
   obs_g_Intro $
   obs_in_Intro $
   obs_out_Intro $
   newNamedVarTable utcpName
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
      [ lmLSunion
      , cjAAlt, cjXXComp
      ]
\end{code}



\begin{code}
utcpName :: String
utcpName = "UTCP"
utcpTheory :: Theory
utcpTheory
  =  nullTheory { thName  =  utcpName
            , thDeps  =  [ utpWC_Name
                         , setName
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