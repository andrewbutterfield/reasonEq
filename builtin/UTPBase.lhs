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

import NiceSymbols

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
     P \sqsupseteq S \defs [P \implies S] &
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
     P \cond b Q \defs (P \land b) \lor (Q \land \lnot b) &
     & \QNAME{$\cond\_$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
condIntro = mkConsIntro i_cond boolf_3
(axCondDef,alCondDef) = bookdef ("cond" -.- "def") "Def2.1.1"
                         (cond p b q === (p /\ b) \/ (mkNot b /\ q))
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

We have a mutual distribution law \cite[Exc 2.1.2,p48]{UTP-book},
for any truth-functional operator $\odot$:

$$
(P \odot Q) \cond b (R \odot S)
=
(P \cond b R) \odot (Q \cond b S)
$$
Does this require us to specify that certain \texttt{Cons} names
should be considered ``schematic''?


\newpage
\subsection{UTP Sequential Composition}

\subsubsection{Defn. of Sequential Composition}

From \cite[Defn 2.2.1,p49]{UTP-book}

$$
  \begin{array}{lll}
     P ; Q \defs \exists O_m \bullet P[O_m/O'] \land Q[O_m/O]
     & m \textrm{ fresh} & \QNAME{$;$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
seqIntro = mkConsIntro i_seq boolf_2
(axSeqDef,alSeqDef) = bookdef (";" -.- "def") "Def2.2.1"
                       ( mkSeq p q
                         === exists [gOm]
                              ( (Sub P p om'sub) /\ (Sub P q omsub) )
                       )
                       scTrue -- for now!
\end{code}

\subsubsection{UTP Seq. Composition Laws}

From \cite[2.2\textbf{L1}, p49]{UTP-book}

$$
  \begin{array}{lll}
     P ; (Q ; R) \equiv (P;Q);R
     && \QNAME{$;$-assoc}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSeqAssoc,alSeqAssoc) = bookdef (";" -.- "assoc") "2.2L1"
                           ( mkSeq p (mkSeq q r) ===  mkSeq (mkSeq p q) r )
                           scTrue
\end{code}


From \cite[2.2\textbf{L2}, p49]{UTP-book}

$$
  \begin{array}{lll}
     (P \cond b Q) ; R \equiv (P;R) \cond b (Q;R)
     && \QNAME{$;$-$\cond\_$-l-distr}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSeqLDistr,alSeqLDistr) = bookdef (";" -.- "cond" -.- "l" -.- "distr") "2.2L2"
                              ( mkSeq (cond p b q) r
                                ===
                                cond (mkSeq p r) b (mkSeq q r)
                              )
                              scTrue
\end{code}

\newpage
\subsection{UTP Assignment}

\subsubsection{Defn. of Assignment}

From \cite[Defn 2.3.1,p50]{UTP-book}

$$
  \begin{array}{lll}
     x := e
     \defs
     x' = e \land O'\less x = O \less x
     && \QNAME{$::=$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
asgIntro = mkConsIntro i_asg apred11
(axAsgDef,alAsgDef) = bookdef (":=" -.- "def") "Def2.3.1"
                       ( ix .:= e
                         ===
                         (x' `isEqualTo` e)
                         /\
                         PIter land equals [ lO' `less` ([ix],[])
                                           , lO  `less` ([ix],[]) ]
                       )
                       scTrue
\end{code}
For now we cannot really handle simultaneous assignment.
It looks like we need to allow general variables to appear as terms.

\subsubsection{UTP Assignment Laws}

From \cite[2.3\textbf{L1}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e  =  (x,y := e,y)
     && \QNAME{$:=$-unchanged}
  \end{array}
$$
This is not definable at present

From \cite[2.3\textbf{L2}, p50]{UTP-book}
$$
  \begin{array}{lll}
     (x,y,z := e,f,g)  =  (y,x,z := f,e,g)
     && \QNAME{$:=$-reorder}
  \end{array}
$$
This is not definable at present

From \cite[2.3\textbf{L3}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e; x := f =  x := f[e/x]
     && \QNAME{$:=$-seq-same}
  \end{array}
$$
\begin{code}
(cjAsgSeqSame,alAsgSeqSame)
  = bookdef (":=" -.- "seq" -.- "same") "2.3L3"
     ( mkSeq (ix .:= e) (ix .:= f)
       ===
       ( ix .:= ESub ArbType f e_for_x )
     )
     scTrue
\end{code}

From \cite[2.3\textbf{L4}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e; P \cond b Q =  (x:=e;P) \cond{b[e/x]} (x:=e;Q)
     && \QNAME{$:=$-seq-$\cond\_$}
  \end{array}
$$
\begin{code}
(cjAsgSeqCond,alAsgSeqCond)
  = bookdef (":=" -.- "seq" -.- "cond") "2.3L4"
     ( mkSeq (ix .:= e) (cond p b q)
       ===
       ( cond (mkSeq (ix .:= e) p)
              (ESub ArbType b e_for_x)
              (mkSeq (ix .:= e) q) )
     )
     scTrue
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
                         ( skip  ===  PIter land equals [ lO', lO ] )
                         scTrue
\end{code}

\subsubsection{UTP Skip Laws}

From \cite[2.3\textbf{L5}, p50]{UTP-book}
$$
  \begin{array}{lll}
     P ; \Skip \equiv P   &
     & \QNAME{$;$-runit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSkipL5a,alSkipL5a) = bookdef (";" -.- "runit") "2.3L5a"
                         (mkSeq p skip === p)
                         scTrue
\end{code}

From \cite[2.3\textbf{L5}, p50]{UTP-book}
$$
  \begin{array}{lll}
     \Skip ; P \equiv P   &
     & \QNAME{$;$-lunit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSkipL5b,alSkipL5b) = bookdef (";" -.- "lunit") "2.3L5b"
                         (mkSeq skip p === p)
                         scTrue
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
     (P \sqcap Q); R = (P;R) \sqcap (Q;R)
     && \QNAME{$;$-$\sqcap$-left-distr-2.4\textbf{L6}}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjSeqNDCLDistr,alSeqNDCLDistr)
   = bookdef (";" -.- "sqcap" -.- "ldistr") "2.4L6"
             ( mkSeq (p `ndc` q) r  ===  (mkSeq p r) `ndc` (mkSeq q r) )
             scTrue
\end{code}

From \cite[2.4\textbf{L7}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P;(Q \sqcap R);  = (P;Q) \sqcap (P;R)
     && \QNAME{$;$-$\sqcap$-right-distr-2.4\textbf{L7}}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjSeqNDCRDistr,alSeqNDCRDistr)
   = bookdef (";" -.- "sqcap" -.- "rdistr") "2.4L7"
             ( mkSeq p (q `ndc` r)  ===  (mkSeq p q) `ndc` (mkSeq p r) )
             scTrue
\end{code}

From \cite[2.4\textbf{L8}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap (Q \cond b R); R = (P \sqcap Q) \cond b (P \sqcap R)
     && \QNAME{$\sqcap$-$\cond\_$-distr-2.4\textbf{L8}}
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
    , cjCondL5b, cjCondL6, cjCondL7, cjCondAlt, cjCondAlt2
    , cjSeqAssoc, cjSeqLDistr
    , cjAsgSeqSame, cjAsgSeqCond
    , cjSkipL5a, cjSkipL5b
    , cjNDCSymm, cjNDCAssoc, cjNDCIdem, cjNDCDistr
    , cjCondNDCDistr, cjSeqNDCLDistr, cjSeqNDCRDistr, cjNDCCondDistr
    ]
\end{code}



We now collect our substitutability information:
\begin{code}
utpBaseSubAbility :: SubAbilityMap
utpBaseSubAbility
 = M.fromList [ ( jId "cond", CS )]
\end{code}

We now collect our alias set:
\begin{code}
utpBaseAliases :: [(String,String)]
utpBaseAliases
  = [ alRefsDef, alRefsOrDistr, alRefsTrans
    , alCondL1, alCondL2, alCondL3, alCondL4
    , alCondL5a, alCondL5b, alCondL6, alCondL7
    , alSeqDef, alSeqAssoc, alSeqLDistr
    , alAsgDef, alAsgSeqSame, alAsgSeqCond
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
            , subable =  utpBaseSubAbility
            , laws    =  utpBaseAxioms
            , conjs   =  utpBaseConjs
            }
\end{code}

\subsection{UTP Base Infrastructure}

Most variables have an ``underlying'' definition
that is then ``wrapped'' in different ways depending on where it is used.

$$P \quad Q \quad R$$
\begin{code}
-- underying variable
vp = Vbl (jId "P") PredV Static
p = fromJust $ pVar vp
q = fromJust $ pVar $ Vbl (jId "Q") PredV Static
r = fromJust $ pVar $ Vbl (jId "R") PredV Static
-- for use in side-conditions
gvP = StdVar vp
\end{code}


$$ b \quad b' \qquad c  \quad c' $$
\begin{code}
b  = fromJust $ pVar $ Vbl (jId "b") PredV Before
b' = fromJust $ pVar $ Vbl (jId "b") PredV After
c  = fromJust $ pVar $ Vbl (jId "c") PredV Before
c' = fromJust $ pVar $ Vbl (jId "c") PredV After
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
iy = jId "y" ; vy  = Vbl iy ObsV Before ; vy' = Vbl iy ObsV After
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
e = fromJust $ eVar int ve
f = fromJust $ eVar int vf
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

$$ O', O, O_m, [O_m/O'], [O_m/O']$$
\begin{code}
o = jId "O"  ;  lO = PreVars o  ;  lO' = PostVars o  ;  lOm = MidVars o "m"
gOm = LstVar lOm
om'sub = jSubstn[] [(lO',lOm)]
omsub  = jSubstn[] [(lO,lOm)]
\end{code}
