\section{UTP Base}
\begin{verbatim}
Copyright  Andrew Buttefield, Danny Thomas (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPBase (
  utpBaseConjs, utpBaseName, utpBaseTheory,
  utpBaseAliases
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
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}


\subsection{Introduction}


By ``UTP Base'' we mean the basic most common UTP definitions
introduced in Chapter 1 and the first part of Chapter 2
in the UTP book \cite{UTP-book}.

The term ``refinement calculus'' is used in the book in Sec. 3.1,
but the refinement notation ($\sqsubseteq$) is not.
The notion of refinement (an implementation $P$ satisfies specification $S$)
is described in Sec 1.5, p34 as being the following closed predicate:
$ [ P \implies S ] $.

In Chapter 2, the concepts of
conditionals,
sequential composition,
assignment,
``Skip'',
and non-deterministic choice are first introduced.
Here we collect those 1st-order concepts.
The higher-order concepts in Chapter 2 are not collected here.

\newpage
\subsection{UTP Refinement}

\subsubsection{Defn. of Refinement}

From \cite[Sec 1.5,p34]{UTP-book},
with addition of the notation using the $\sqsupseteq$ symbol:
$$
  \begin{array}{lll}
     P \sqsupseteq Q \defs [P \implies Q] &
     & \QNAME{$\sqsupseteq$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
refinesIntro = mkConsIntro i_refines boolf_2
(axRefsDef,alRefsDef) = bookdef ("sqsupseteq" -.- "def") "defd1.5p34"
                         (refines p q === univ (p ==> q))
                         scTrue
\end{code}

\subsubsection{UTP Refinement Laws}


From \cite[Sec 1.5,p35]{UTP-book}
$$
  \begin{array}{lll}
     (P \lor Q \sqsupseteq R)
     \equiv
     (P \sqsupseteq R) \land (Q \sqsupseteq R)  &
     & \QNAME{$\sqsupseteq$-$\lor$-distr}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjRefsOrDistr,alRefsOrDistr)
  = bookdef ("sqsupseteq" -.- "lor" -.- "distr") "assrt1.5p35"
            ( (p \/ q) `refines` r
              ===
              (p `refines` r) /\ (q `refines` r))
            scTrue
\end{code}

From \cite[Sec 1.5,pp35-36]{UTP-book}
$$
  \begin{array}{lll}
     (P \sqsupseteq Q) \land (Q \sqsupseteq R) \implies (P \sqsupseteq R)  &
     & \QNAME{$\sqsupseteq$-trans}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjRefsTrans,alRefsTrans)
  = bookdef ("sqsupseteq" -.- "trans") "assrt1.5p36a"
            ( (p `refines` q) /\ (q `refines` r)
              ==>
              (p `refines` r) )
            scTrue
\end{code}

Other ``laws'' regarding refinement in Chapter 1:

$$
 [D \land E \implies S] \land [P \implies D] \land [Q \implies E]
 \implies
 [P \land Q \implies S]
 \qquad\textrm{p36}
$$

$$
 F\textrm{ monotonic} \land [Y \implies X] \implies [F(X)\implies F(Y)]
 \qquad\textrm{p37}
$$

$$
[X \land Q \implies S]
\equiv
[X \implies (\forall \lst x \bullet Q \implies S)]
, \textrm{ given }\lst x \notin X
\qquad\textrm{p39}
$$

$$
  [ ( \exists \lst c \bullet D(\lst c)
      \land L(\lst c,\lst a) )
    \implies S(\lst a)
  ]
  \equiv
  [ D(\lst c)
    \implies
    ( \forall \lst a \bullet L(\lst c,\lst a) \implies S(\lst a) )
  ]
, \textrm{ given }\lst c \not{\!\cap}\; \lst a
  \qquad\textrm{p41}
$$

We may implement these later.

\newpage
\subsection{UTP Conditionals}

\subsubsection{Defn. of Conditional}

From \cite[Defn 2.1.1,p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b Q \defs (b \land P) \lor (\lnot b \land Q) &
     & \QNAME{$\cond\_$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
condIntro = mkConsIntro i_cond boolf_3
(axCondDef,alCondDef) = bookdef ("cond" -.- "def") "Def2.1.1"
                         (cond p b q === (b /\ p) \/ (mkNot b /\ q))
                         scTrue
\end{code}


\subsubsection{UTP Conditional Laws}

From \cite[2.1\textbf{L1}, p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b P \equiv P  &
     & \QNAME{$\cond\_$-idem}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL1,alCondL1) = bookdef ("cond" -.- "idem") "2.1L1"
                       (cond p b p === p)
                       scTrue
\end{code}

From \cite[2.1\textbf{L2}, p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b P \equiv Q \cond{\lnot b} P  &
     & \QNAME{$\cond\_$-idem}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL2,alCondL2) = bookdef ("cond" -.- "symm") "2.1L2"
                       (cond p b q === cond q (mkNot b) p)
                       scTrue
\end{code}

From \cite[2.1\textbf{L3}, p47]{UTP-book}
$$
  \begin{array}{lll}
     ( P \cond b Q) \cond c R
       \equiv
       P \cond{b \land c} ( Q \cond c R)  &
     & \QNAME{$\cond\_$-assoc}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL3,alCondL3) = bookdef ("cond" -.- "assoc") "2.1L3"
                       ( cond (cond p b q) c r
                         ===
                         cond p (b /\ c) (cond q c r) )
                       scTrue
\end{code}

From \cite[2.1\textbf{L4}, p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b (Q \cond c R)
       \equiv
       (P \cond b Q) \cond c ( P \cond b R)  &
     & \QNAME{$\cond\_$-distr}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL4,alCondL4) = bookdef ("cond" -.- "distr")  "2.1L4"
                       ( cond p b (cond q c r)
                         ===
                         cond (cond p b q) c (cond p b r) )
                       scTrue
\end{code}

From \cite[2.1\textbf{L5}, p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond \true Q \equiv P   &
     & \QNAME{$\cond\_$-runit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL5a,alCondL5a) = bookdef ("cond" -.- "runit") "2.1L5a"
                         (cond p trueP q === p)
                         scTrue
\end{code}

From \cite[2.1\textbf{L5}, p47]{UTP-book}
$$
  \begin{array}{lll}
     Q \cond \false P \equiv P   &
     & \QNAME{$\cond\_$-lunit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL5b,alCondL5b) = bookdef ("cond" -.- "lunit") "2.1L5b"
                         (cond q falseP p === p)
                         scTrue
\end{code}

From \cite[2.1\textbf{L6}, p48]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b (Q \cond b R) \equiv P \cond b R  &
     & \QNAME{$\cond\_$-absorb}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL6,alCondL6) = bookdef ("cond" -.- "absorb") "2.1L6"
                       (cond p b (cond q b r) === cond p b r)
                       scTrue
\end{code}

From \cite[2.1\textbf{L7}, p48]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b (P \cond c Q) \equiv P \cond{b \lor c} Q  &
     & \QNAME{$\cond\_$-merge}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjCondL7,alCondL7) = bookdef ("cond" -.- "merge") "2.1L7"
                       (cond p b (cond p c q) === cond p (b \/ c) q)
                       scTrue
\end{code}

From \cite[Ex. 2.1.2, p48]{UTP-book},
for any truth-functional operator $\odot$,
show:
$$
  \begin{array}{lll}
     (P \odot Q) \cond b (R \odot S)
     \equiv
     (P \cond b R) \odot (Q \cond b S)  &
     & \QNAME{$\cond\_$-mutual-distr}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
tfo p q = Cons P True (jId "star") [p,q]
(cjCondMutual,alCondMutual)
  = bookdef ("cond" -.- "mdistr") "Ex2.1.2"
      ( cond (p `tfo` q) b (r `tfo` s) === tfo (cond p b r) (cond q b s) )
      scTrue
\end{code}


The following conjectures are not in the book,
but can be useful:
$$
  \begin{array}{lll}
     P \cond b Q \equiv (b \implies P) \land (\lnot b \implies Q)
     && \QNAME{$\cond\_$-alt-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjCondAlt = preddef ("cond" -.- "alt" -.- "def")
                     (cond p b q === (b ==> p) /\ (mkNot b ==> q))
                     scTrue
\end{code}

$$
  \begin{array}{lll}
     P \cond b Q \equiv (\lnot b \lor P) \equiv (b \lor Q)
     && \QNAME{$\cond\_$-alt-def2}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjCondAlt2 = preddef ("cond" -.- "alt" -.- "def2")
                     (cond p b q === ((mkNot b \/ p) === (b \/ q)))
                     scTrue
\end{code}


\newpage
\subsection{UTP Sequential Composition}

\subsubsection{Defn. of Sequential Composition}

We need to know when a predicate is a UTP predicate ($O \cup O'\supseteq P$).
We will do this by defining a \emph{uniform} side-condition ($O \supseteq p$).
\begin{code}
assertIsUTP  :: GenVar -> SideCond
assertIsUTP  gP  = [gO,gO'] `covers` gP
assertAreUTP :: [GenVar] -> SideCond
assertAreUTP gPs = mrgscs $ map assertIsUTP gPs
\end{code}
We also want to be able to specify a UTP condition ($O \subseteq c$):
\begin{code}
assertIsUTPCond  :: GenVar -> SideCond
assertIsUTPCond  gP  = [gO] `covers` gP
assertAreUTPCond :: [GenVar] -> SideCond
assertAreUTPCond gPs = mrgscs $ map assertIsUTPCond gPs
\end{code}


From \cite[Defn 2.2.1,p49]{UTP-book}

$$
  \begin{array}{lll}
     P \seq Q \defs \exists O_0 \bullet P[O_0/O'] \land Q[O_0/O]
     & O,O'\supseteq P,Q ~~ O_0 \textrm{ fresh}
     & \QNAME{$;$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
seqIntro = mkConsIntro i_seq boolf_2
(axSeqDef,alSeqDef) = bookdef (";" -.- "def") "Def2.2.1"
                       ( mkSeq p q
                         === exists [gO0]
                              ( (Sub P p o0'sub) /\ (Sub P q o0sub) )
                       )
                       (assertIsUTP gp .: assertIsUTP gq .: gfresh)
   where
      gfresh = fresh $ S.singleton gO0
\end{code}
We want to assert $O \supseteq P$, and rely on unformity to get the rest.

We also need to ensure that $O$, $O'$, and $O_m$ are ``known''.
\begin{code}
obsIntro = fromJust . addKnownVarSet vO S.empty
\end{code}
We need to be able to make use of the following properties in proofs:
$$
  O \cup O' \supseteq P \qquad O \cup O' \supseteq Q \qquad \dots
$$

\subsubsection{UTP Seq. Composition Laws}

From \cite[2.2\textbf{L1}, p49]{UTP-book}

$$
  \begin{array}{lll}
     P \seq (Q \seq R) \equiv (P\seq Q)\seq R
     & O,O'\supseteq P,Q,R
     & \QNAME{$;$-assoc}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSeqAssoc,alSeqAssoc) = bookdef (";" -.- "assoc") "2.2L1"
                           ( mkSeq p (mkSeq q r) ===  mkSeq (mkSeq p q) r )
                           (assertAreUTP [gP,gQ,gR] )
\end{code}


From \cite[2.2\textbf{L2}, p49]{UTP-book}

$$
  \begin{array}{lll}
     (P \cond b Q) \seq R \equiv (P\seq R) \cond b (Q\seq R)
     & O,O'\supseteq P,Q,R ~~ O \supseteq b
     & \QNAME{$;$-$\cond\_$-l-distr}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSeqLDistr,alSeqLDistr) = bookdef (";" -.- "cond" -.- "l" -.- "distr") "2.2L2"
                              ( mkSeq (cond p b q) r
                                ===
                                cond (mkSeq p r) b (mkSeq q r)
                              )
                              (assertAreUTP [gP,gQ,gR] .: assertIsUTPCond gb)
\end{code}

\newpage
\subsection{UTP Assignment}

\subsubsection{Defn. of Assignment}

From \cite[Defn 2.3.1,p50]{UTP-book}

We start by defining simultaneous assignment,
based loosely on \cite[2.3\textbf{L2}, p50]{UTP-book}.
$$
  \begin{array}{lll}
     \lst x := \lst e
     \defs
     \lst x' = \lst e \land O'\less {\lst x} = O \less {\lst x}
     && \QNAME{$:=$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
asgIntro = mkConsIntro i_asg apred11
(axAsgDef,alAsgDef) = bookdef (":=" -.- "def") "2.3L2"
                       ( lvxs .::= lves
                         ===
                         (lvx' `areEqualTo` lves)
                         /\
                         ( (lO' `less` ([],[ix]))
                           `areEqualTo`
                           (lO  `less` ([],[ix])) )
                       )
                       scTrue
\end{code}



\subsubsection{UTP Assignment Laws}

We start with another axiom that describes the ``fusion'' of predicates
over lists of variables, structured in a particular way:
$$
  P(x_1,y_1) \diamond P(x_2,y_2) \diamond \dots \diamond P(x_n,y_n)
$$
Here $P(x_i,y_i)$ is a binary predicate
whose only free variables are $x_i$ and $y_i$,
while $\diamond$ is an associative and commutative
binary propositional operator.
We are interested in a form that mixes standard and \emph{known} list variables,
and where, for any given $i$,
that $(x_i,y_i)$ is equal to $(v,v')$ for some $v$:
$$
  \dots \diamond P(v,v') \diamond \dots \diamond P(O\less V,O'\less V) \diamond \dots
$$
By ``fusion'' we mean simplifying the above by observing that
$\setof{v,O\less V}$ can be reduced to $\setof{O\less{(V\setminus\setof{v})}}$
if $v \in V$.
This leads to the following general axiom,
in which all variables are list-variables:
$$
  \begin{array}{lll}
     P(\lst x',\lst x)
     \diamond
     P(O' \less{\lst x,\lst y},O \less{\lst x,\lst y})
     \defs
     P(O' \less{\lst y},O \less{\lst y})
     && \QNAME{var-list-fusion}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
axFusionDef
  = preddef ("var" -.- "list" -.- "fusion")
            ( fusion [ (lvx',lvx)
                     , ( lO' `less` ([],[ix,iy]), (lO `less` ([],[ix,iy])) ) ]
              ===
              fusion [ ( lO' `less` ([],[iy]), (lO `less` ([],[iy])) ) ]
            )
            scTrue
  where
    fusion lvlvs  =  listwiseVarBinPred P land equals [] lvlvs
\end{code}


\newpage
The following (\cite[Defn 2.3.1,p50]{UTP-book}) is now a conjecture:
$$
  \begin{array}{lll}
     x := e
     \defs
     x' = e \land O'\less x = O \less x
     && \QNAME{$:=$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjAsgSimple,alAsgSimple) = bookdef (":=" -.- "simple") "Def2.3.1"
                       ( vx .:= e
                         ===
                         (x' `isEqualTo` e)
                         /\
                         ( (lO' `less` ([ix],[]))
                           `areEqualTo`
                           (lO  `less` ([ix],[])) )
                       )
                       scTrue
\end{code}


From \cite[2.3\textbf{L1}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e  =  (x,y := e,y)
     && \QNAME{$:=$-unchanged}
  \\ = x' = e \land y' = y \land O'\less {\lst x,\lst y} = O \less {\lst x, \lst y}
  \end{array}
$$
\begin{code}
(cjAsgUnchanged,alAsgUnchanged)
  = bookdef (":=" -.- "unchanged") "2.3L3"
     ( (vx .:= e)
       ===
       simassign [(vx,e),(vy,y)] []
     )
     scTrue
\end{code}



From \cite[2.3\textbf{L2}, p50]{UTP-book}
$$
  \begin{array}{lll}
     (x,y,z := e,f,g)  =  (y,x,z := f,e,g)
     && \QNAME{$:=$-reorder}
  \end{array}
$$
This property is guaranteed by the use of substitution as the underlying
representation.

\newpage
From \cite[2.3\textbf{L3}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e \seq x := f =  x := f[e/x]
     & x,e,f \in O
     & \QNAME{$:=$-seq-same}
  \end{array}
$$
\begin{code}
(cjAsgSeqSame,alAsgSeqSame)
  = bookdef (":=" -.- "seq" -.- "same") "2.3L3"
     ( mkSeq (vx .:= e) (vx .:= f)
       ===
       ( vx .:= ESub ArbType f e_for_x )
     )
     (assertAreUTPCond [gx,qe,qf])
\end{code}

From \cite[2.3\textbf{L4}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e \seq P \cond b Q =  (x:=e \seq P) \cond{b[e/x]} (x:=e \seq Q)
     & x,e,b \in O, ~~ O,O'\supseteq P,Q
     & \QNAME{$:=$-seq-$\cond\_$}
  \end{array}
$$
\begin{code}
(cjAsgSeqCond,alAsgSeqCond)
  = bookdef (":=" -.- "seq" -.- "cond") "2.3L4"
     ( mkSeq (vx .:= e) (cond p b q)
       ===
       ( cond (mkSeq (vx .:= e) p)
              (ESub ArbType b e_for_x)
              (mkSeq (vx .:= e) q) )
     )
     (assertAreUTP [gP,gQ] .: assertAreUTPCond [gx,qe,gb])
\end{code}

\newpage
\subsection{UTP ``Skip''}

\subsubsection{Defn. of Skip}

From \cite[Defn 2.3.2,p50]{UTP-book}

$$
  \begin{array}{lll}
     \Skip \defs O' = O
     && \QNAME{$\Skip$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
skipIntro = mkConsIntro i_skip bool
(axSkipDef,alSkipDef) = bookdef ("II" -.- "def") "Def2.3.2"
                         ( skip  ===  PIter True land True equals [ lO', lO ] )
                         scTrue
\end{code}

\subsubsection{UTP Skip Laws}

From \cite[2.3\textbf{L5}, p50]{UTP-book}
$$
  \begin{array}{lll}
     R \seq \Skip \equiv R   & O,O'\supseteq R
     & \QNAME{$;$-runit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSkipL5a,alSkipL5a) = bookdef (";" -.- "runit") "2.3L5a"
                         (mkSeq r skip === r)
                         (assertAreUTP [gR,g_skip])
\end{code}

From \cite[2.3\textbf{L5}, p50]{UTP-book}
$$
  \begin{array}{lll}
     \Skip \seq R \equiv R   & O,O'\supseteq R
     & \QNAME{$;$-lunit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSkipL5b,alSkipL5b) = bookdef (";" -.- "lunit") "2.3L5b"
                         (mkSeq skip r === r)
                         (assertAreUTP [gR,g_skip])
\end{code}


\newpage
\subsection{UTP Non-deterministic Choice}

\subsubsection{Defn. of N.-D.-Choice}

From \cite[Defn 2.4.1,p51]{UTP-book}

$$
  \begin{array}{lll}
     P \sqcap Q = P \lor Q
     && \QNAME{$\sqcap$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
v_ndc = Vbl i_ndc PredV Static
ndcIntro = mkConsIntro i_ndc boolf_2
(axNDCDef,alNDCDef) = bookdef ("sqcap" -.- "def") "Def2.4.1"
                         ( p `ndc` q  ===  p \/ q )
                         scTrue
\end{code}

\subsubsection{UTP N.-D.-Choice Laws}

From \cite[2.4\textbf{L1}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap Q = P \lor Q
     && \QNAME{$\sqcap$-symm}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCSymm,alNDCSymm) = bookdef ("sqcap" -.- "symm") "2.4L1"
                         ( p `ndc` q  ===  q `ndc` p )
                         scTrue
\end{code}

From \cite[2.4\textbf{L2}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap Q = P \lor Q
     && \QNAME{$\sqcap$-symm}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCAssoc,alNDCAssoc) = bookdef ("sqcap" -.- "assoc") "2.4L2"
                         ( p `ndc` (q `ndc` r)  ===  (p `ndc` q) `ndc` r )
                         scTrue
\end{code}

From \cite[2.4\textbf{L3}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap P = P
     && \QNAME{$\sqcap$-idemp}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCIdem,alNDCIdem) = bookdef ("sqcap" -.- "idem") "2.4L3"
                         ( p `ndc` p  ===  p )
                         scTrue
\end{code}

From \cite[2.4\textbf{L4}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap (Q \sqcap R) = (P \sqcap Q) \sqcap (P \sqcap R)
     && \QNAME{$\sqcap$-self-distr}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCDistr,alNDCDistr)
   = bookdef ("sqcap" -.- "distr") "2.4L4"
             ( p `ndc` (q `ndc` r)  ===  (p `ndc` q) `ndc` (p `ndc` r) )
             scTrue
\end{code}


From \cite[2.4\textbf{L5}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b (Q \sqcap R) = (P \cond b Q) \sqcap (P \cond b R)
     && \QNAME{$\cond\_$-$\sqcap$-distr-2.4\textbf{L5}}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjCondNDCDistr,alCondNDCDistr)
   = bookdef ("cond" -.- "sqcap" -.- "distr") "2.4L5"
             ( cond p b (q `ndc` r)  ===  (cond p b q) `ndc` (cond p b r) )
             scTrue
\end{code}

\newpage

From \cite[2.4\textbf{L6}, p52]{UTP-book}
$$
  \begin{array}{lll}
     (P \sqcap Q) \seq R = (P \seq R) \sqcap (Q \seq R)
     & O,O'\supseteq P,Q,R
     & \QNAME{$;$-$\sqcap$-left-distr-2.4\textbf{L6}}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjSeqNDCLDistr,alSeqNDCLDistr)
   = bookdef (";" -.- "sqcap" -.- "ldistr") "2.4L6"
             ( mkSeq (p `ndc` q) r  ===  (mkSeq p r) `ndc` (mkSeq q r) )
             (assertAreUTP [gP,gQ,gR])
\end{code}

From \cite[2.4\textbf{L7}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \seq (Q \sqcap R) \seq   = (P \seq Q) \sqcap (P \seq R)
     & O,O'\supseteq P,Q,R
     & \QNAME{$;$-$\sqcap$-right-distr-2.4\textbf{L7}}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjSeqNDCRDistr,alSeqNDCRDistr)
   = bookdef (";" -.- "sqcap" -.- "rdistr") "2.4L7"
             ( mkSeq p (q `ndc` r)  ===  (mkSeq p q) `ndc` (mkSeq p r) )
             (assertAreUTP [gP,gQ,gR])
\end{code}

From \cite[2.4\textbf{L8}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap (Q \cond b R)\seq R = (P \sqcap Q) \cond b (P \sqcap R)
     & & \QNAME{$\sqcap$-$\cond\_$-distr-2.4\textbf{L8}}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCCondDistr,alNDCCondDistr)
   = bookdef ("sqcap" -.- "cond" -.- "distr") "2.4L8"
             ( p `ndc` (cond q b r)  ===  cond (p `ndc` q) b (p `ndc` r) )
             scTrue
\end{code}

\newpage
\subsection{UTP Abort}

\subsubsection{Defn. of Abort}

From \cite[Defn 2.4.2,p53]{UTP-book}

$$
  \begin{array}{lll}
     \bot  = \true
     && \QNAME{$\bot$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
abortIntro = mkConsIntro i_abort bool
(axAbortDef,alAbortDef) = bookdef ("bot" -.- "def") "Def2.4.2"
                           ( abort  ===  trueP )
                           scTrue
\end{code}

\subsection{UTP Miracle}

\subsubsection{Defn. of Miracle}

From \cite[Defn 2.5.1,p55]{UTP-book}

$$
  \begin{array}{lll}
     \top  = \false
     && \QNAME{$\top$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
miracleIntro = mkConsIntro i_miracle bool
(axMiracleDef,alMiracleDef) = bookdef ("top" -.- "def") "Def2.5.1"
                           ( miracle  ===  falseP )
                           scTrue
\end{code}

\newpage
\subsection{UTP Base Theory}

We collect our known variables:
\begin{code}
utpBaseKnown
 = refinesIntro $
   condIntro $
   seqIntro $
   obsIntro $
   asgIntro $
   skipIntro $
   ndcIntro $
   abortIntro $
   miracleIntro $
   newVarTable
\end{code}


We now collect our axiom set:
\begin{code}
utpBaseAxioms :: [Law]
utpBaseAxioms
  = map labelAsAxiom
      [ axRefsDef
      , axCondDef
      , axSeqDef
      , axAsgDef
      , axFusionDef
      , axSkipDef
      , axNDCDef
      , axAbortDef, axMiracleDef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpBaseConjs :: [NmdAssertion]
utpBaseConjs
  = [ cjRefsOrDistr, cjRefsTrans
    , cjCondL1, cjCondL2, cjCondL3, cjCondL4, cjCondL5a
    , cjCondL5b, cjCondL6, cjCondL7, cjCondMutual, cjCondAlt, cjCondAlt2
    , cjSeqAssoc, cjSeqLDistr
    , cjAsgSimple, cjAsgUnchanged, cjAsgSeqSame, cjAsgSeqCond
    , cjSkipL5a, cjSkipL5b
    , cjNDCSymm, cjNDCAssoc, cjNDCIdem, cjNDCDistr
    , cjCondNDCDistr, cjSeqNDCLDistr, cjSeqNDCRDistr, cjNDCCondDistr
    ]
\end{code}


We now collect our alias set:
\begin{code}
utpBaseAliases :: [(String,String)]
utpBaseAliases
  = [ alRefsDef, alRefsOrDistr, alRefsTrans
    , alCondL1, alCondL2, alCondL3, alCondL4
    , alCondL5a, alCondL5b, alCondL6, alCondL7
    , alCondMutual
    , alSeqDef, alSeqAssoc, alSeqLDistr
    , alAsgDef, alAsgUnchanged, alAsgSeqSame, alAsgSeqCond
    , alSkipDef, alSkipL5a, alSkipL5b
    , alNDCDef, alNDCSymm, alNDCAssoc, alNDCIdem, alNDCDistr
    , alCondNDCDistr, alSeqNDCLDistr, alSeqNDCRDistr, alNDCCondDistr
    , alAbortDef, alMiracleDef
    ]
\end{code}


\begin{code}
utpBaseName :: String
utpBaseName = "UTPBase"
utpBaseTheory :: Theory
utpBaseTheory
  =  nullTheory { thName  =  utpBaseName
            , thDeps  =  [ uCloseName
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
            , known   =  utpBaseKnown
            , laws    =  utpBaseAxioms
            , conjs   =  utpBaseConjs
            }
\end{code}

\subsection{UTP Base Infrastructure}

Most variables have an ``underlying'' definition
that is then ``wrapped'' in different ways depending on where it is used.

$$P \quad Q \quad R \quad S$$
\begin{code}
vP = Vbl (jId "P") PredV Static ; p = fromJust $ pVar vP ; gP = StdVar vP
vQ = Vbl (jId "Q") PredV Static ; q = fromJust $ pVar vQ ; gQ = StdVar vQ
vR = Vbl (jId "R") PredV Static ; r = fromJust $ pVar vR ; gR = StdVar vR
vS = Vbl (jId "S") PredV Static ; s = fromJust $ pVar vS ; gS = StdVar vS
\end{code}
For uniform side-conditions:
\begin{code}
gp = StdVar $ Vbl (jId "P") PredV Before
gq = StdVar $ Vbl (jId "Q") PredV Before
\end{code}




$$ b \quad b' \qquad c  \quad c' $$
\begin{code}
vb  = Vbl (jId "b") PredV Before; b  = fromJust $ pVar vb;  gb  = StdVar vb
vb' = Vbl (jId "b") PredV After;  b' = fromJust $ pVar vb'; gb' = StdVar vb'
vc  = Vbl (jId "c") PredV Before; c  = fromJust $ pVar vc;  gc  = StdVar vc
vc' = Vbl (jId "c") PredV After;  c' = fromJust $ pVar vc'; gc' = StdVar vc'
\end{code}


$$ v \qquad \lst v $$
\begin{code}
(v,vs) = (StdVar vv, LstVar lvvs)
  where
   vv   = Vbl (jId "v") ObsV Static
   lvvs = LVbl vv [] []
\end{code}

$$ x \quad y \quad z \qquad x' \quad y' \quad z'$$

Underlying variables:
\begin{code}
ix = jId "x" ; vx  = Vbl ix ObsV Before ; vx' = Vbl ix ObsV After
lvx = LVbl vx [] []; lvx' = LVbl vx' [] []
gx = StdVar vx
iy = jId "y" ; vy  = Vbl iy ObsV Before ; vy' = Vbl iy ObsV After
lvy = LVbl vy [] []
iz = jId "z" ; vz  = Vbl iz ObsV Before ; vz' = Vbl iz ObsV After
\end{code}

For use in expressions  and substitution first list
\\(e.g. $x+y$ might be \texttt{plus [x,y]}):
\begin{code}
[x,y,z,x',y',z'] = map (fromJust . eVar ArbType) [vx,vy,vz,vx',vy',vz']
\end{code}

For use in quantifier variable list/sets and substitution second lists
\\(e.g. $\forall x,x' \bullet P$ would be \texttt{forall [qx,qx'] p}):
\begin{code}
[qx,qy,qz,qx',qy',qz'] = map StdVar [vx,vy,vz,vx',vy',vz']
\end{code}

$$ x_m \qquad y_m \qquad z_m$$
For use in quantifier variable list/sets and substitutions:
\begin{code}
xm = StdVar $ Vbl (jId "x") ObsV (During "m")
\end{code}

$$\Nat \qquad \Int$$
\begin{code}
nat  = GivenType $ jId "N"
int  = GivenType $ jId "Z"
\end{code}

$$ e \quad \lst e  \qquad f \quad \lst f$$
\begin{code}
-- Underlying variables:
ve = Vbl (jId "e") ExprV Before
vf = Vbl (jId "f") ExprV Before
-- for use in expressions
e = fromJust $ eVar ArbType ve
f = fromJust $ eVar ArbType vf
-- for use in quantifiers, substitutions (first list)
qe = StdVar ve
qf = StdVar vf
-- list versions, for use in substitutions (second list)
lves = LVbl ve [] []
lvfs = LVbl vf [] []
-- for use in quantifiers, side-conditions
qes = LstVar lves
qfs = LstVar lvfs
\end{code}

$$ P[e/x] \qquad P[\lst e/\lst x]$$
\begin{code}
-- note that [ a / v]  becomes (v,a) !
e_for_x = jSubstn [(vx,e)] []
sub p = Sub P p e_for_x
lvxs = LVbl vx [] []
qxs = LstVar lvxs
lsub p = Sub P p $ jSubstn[] [(lvxs,lves)]
\end{code}

$$ O', O, O_0, [O_0/O'], [O_0/O']$$
\begin{code}
o = jId "O"  ;  vO = PreVar o
lO = PreVars o  ;  lO' = PostVars o  ;  lO0 = MidVars o "0"
gO = LstVar lO  ;  gO' = LstVar lO'  ;  gO0 = LstVar lO0
o0'sub = jSubstn[] [(lO',lO0)]
o0sub  = jSubstn[] [(lO,lO0)]
\end{code}
