\chapter{UTP Common While}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.While.Common (
  utpCW_Conjs, utpCW_Name, utpCW_Theory
, utpCW_Aliases
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
import UTP.Observations
import UTP.While.RefineSig
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we give semantics to elements of the ``While'' signature
whose definitions do not change 
when we move from na\"{i}ve to design-based theories.



In \cite[Thm 3.1.4, p79]{UTP-book} it is claimed that 
NDC, conditionals and sequential composition have unchanged definitions.
Finally, \cite[Thm 3.1.5, p80]{UTP-book} states that designs form
a complete lattice under implication ordering, 
with bottom $\bot_{\mathbf{D}}=(\false\design\true)$
and top $\top_{\mathbf{D}}=(\true\design\false)=\lnot ok$.
This means the semantics of the while-loop is essentially the same.

These are everything except skip assignment,
which have different definitions in each.


\newpage
\section{UTP Refinement}

\subsection{Defn. of Refinement}

From \cite[Sec 1.5,p34]{UTP-book},
with addition of the notation using the $\sqsupseteq$ symbol:
$$
  \begin{array}{lll}
     P \sqsupseteq Q ~\defs~ [P \implies Q] &
     & \QNAME{$\sqsupseteq$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
refinesIntro = mkConsIntro i_refines boolf_2
(axRefsDef,alRefsDef) = bookdef ("refines" -.- "def") "defd1.5p34"
                         (refines p q === univ (p ==> q))
                         scTrue
\end{code}

\subsection{UTP Refinement Laws}


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
  = bookdef ("refines" -.- "lor" -.- "distr") "assrt1.5p35"
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
  = bookdef ("refines" -.- "trans") "assrt1.5p36a"
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
\section{UTP Conditionals}

\subsection{Defn. of Conditional}

From \cite[Defn 2.1.1,p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b Q ~\defs~ (b \land P) \lor (\lnot b \land Q) &
     & \QNAME{$\cond\_$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
condIntro = mkConsIntro i_cond boolf_3
(axCondDef,alCondDef) = bookdef ("cond" -.- "def") "Def2.1.1"
                         (cond p b q === (b /\ p) \/ (mkNot b /\ q))
                         scTrue
\end{code}


\subsection{UTP Conditional Laws}

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
tfo p q = Cons pred1 True (jId "star") [p,q]
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
\section{UTP Sequential Composition}


From \cite[Defn 2.2.1,p49]{UTP-book}

$$
  \begin{array}{lll}
     P \seq Q ~\defs~ \exists O_0 \bullet P[O_0/O'] \land Q[O_0/O]
     & O,O'\supseteq_a P,Q ~~ O_0 \textrm{ fresh}
     & \QNAME{$;$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
seqIntro = mkConsIntro i_seq boolf_2
(axSeqDef,alSeqDef) = bookdef (";" -.- "def") "Def2.2.1"
                       ( mkSeq p q
                         === exists [gO0]
                              ( (Sub pred1 p o0'sub) /\ (Sub pred1 q o0sub) )
                       )
                       (isUTPDynObs gp .: isUTPDynObs gq .: gfresh)
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

\subsection{UTP Seq. Composition Laws}

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
                           (areUTPDynObs [gP,gQ,gR] )
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
                              (areUTPDynObs [gP,gQ,gR] .: isUTPCond gb)
\end{code}

\newpage
\section{UTP Non-deterministic Choice}

\subsection{Defn. of N.-D.-Choice}

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

\subsection{UTP N.-D.-Choice Laws}

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
             (areUTPDynObs [gP,gQ,gR])
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
             (areUTPDynObs [gP,gQ,gR])
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


\section{Variable List Fusion}

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
     ~\defs~
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
    fusion lvlvs  =  listwiseVarBinPred pred1 land equals [] lvlvs
\end{code}


\newpage
\section{UTP Base Theory}

We collect our known variables:
\begin{code}
utpCW_Known
 = refinesIntro $
   condIntro $
   seqIntro $
   obsIntro $
   ndcIntro $
   newNamedVarTable utpCW_Name
\end{code}


We now collect our axiom set:
\begin{code}
utpCW_Axioms :: [Law]
utpCW_Axioms
  = map labelAsAxiom
      [ axRefsDef
      , axCondDef
      , axSeqDef
      , axFusionDef
      , axNDCDef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpCW_Conjs :: [NmdAssertion]
utpCW_Conjs
  = [ cjRefsOrDistr, cjRefsTrans
    , cjCondL1, cjCondL2, cjCondL3, cjCondL4, cjCondL5a
    , cjCondL5b, cjCondL6, cjCondL7, cjCondMutual, cjCondAlt, cjCondAlt2
    , cjSeqAssoc, cjSeqLDistr
    , cjNDCSymm, cjNDCAssoc, cjNDCIdem, cjNDCDistr
    , cjCondNDCDistr, cjSeqNDCLDistr, cjSeqNDCRDistr, cjNDCCondDistr
    ]
\end{code}


We now collect our alias set:
\begin{code}
utpCW_Aliases :: [(String,String)]
utpCW_Aliases
  = [ alRefsDef, alRefsOrDistr, alRefsTrans
    , alCondL1, alCondL2, alCondL3, alCondL4
    , alCondL5a, alCondL5b, alCondL6, alCondL7
    , alCondMutual
    , alSeqDef, alSeqAssoc, alSeqLDistr
    , alNDCDef, alNDCSymm, alNDCAssoc, alNDCIdem, alNDCDistr
    , alCondNDCDistr, alSeqNDCLDistr, alSeqNDCRDistr, alNDCCondDistr
    ]
\end{code}


\begin{code}
utpCW_Name :: String
utpCW_Name = "U_CWhl"
utpCW_Theory :: Theory
utpCW_Theory
  =  nullTheory { thName  =  utpCW_Name
                , thDeps  = [ uCloseName
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
            , known   =  utpCW_Known
            , laws    =  utpCW_Axioms
            , conjs   =  utpCW_Conjs
            }
\end{code}

\section{UTP Base Infrastructure}

Most variables have an ``underlying'' definition
that is then ``wrapped'' in different ways depending on where it is used.

$$P \quad Q \quad R \quad S$$
\begin{code}
vP = Vbl (jId "P") PredV Static ; p = fromJust $ pVar ArbType vP ; gP = StdVar vP
vQ = Vbl (jId "Q") PredV Static ; q = fromJust $ pVar ArbType vQ ; gQ = StdVar vQ
vR = Vbl (jId "R") PredV Static ; r = fromJust $ pVar ArbType vR ; gR = StdVar vR
vS = Vbl (jId "S") PredV Static ; s = fromJust $ pVar ArbType vS ; gS = StdVar vS
\end{code}
For uniform side-conditions:
\begin{code}
gp = StdVar $ Vbl (jId "P") PredV Before
gq = StdVar $ Vbl (jId "Q") PredV Before
\end{code}




$$ b \quad b' \qquad c  \quad c' $$
\begin{code}
vb  = Vbl (jId "b") PredV Before; b  = fromJust $ pVar ArbType vb;  gb  = StdVar vb
vb' = Vbl (jId "b") PredV After;  b' = fromJust $ pVar ArbType vb'; gb' = StdVar vb'
vc  = Vbl (jId "c") PredV Before; c  = fromJust $ pVar ArbType vc;  gc  = StdVar vc
vc' = Vbl (jId "c") PredV After;  c' = fromJust $ pVar ArbType vc'; gc' = StdVar vc'
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
sub p = Sub pred1 p e_for_x
lvxs = LVbl vx [] []
qxs = LstVar lvxs
lsub p = Sub pred1 p $ jSubstn[] [(lvxs,lves)]
\end{code}

$$ O', O, O_0, [O_0/O'], [O_0/O']$$
\begin{code}
o = jId "O"  ;  vO = PreVar o
lO = PreVars o  ;  lO' = PostVars o  ;  lO0 = MidVars o "0"
gO = LstVar lO  ;  gO' = LstVar lO'  ;  gO0 = LstVar lO0
o0'sub = jSubstn[] [(lO',lO0)]
o0sub  = jSubstn[] [(lO,lO0)]
\end{code}
