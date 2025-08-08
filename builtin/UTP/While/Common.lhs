\chapter{UTP While Theory}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.While.Common (
  i_cond, cond
, i_seq, mkSeq
, i_while, while
, listwiseVarBinPred
, i_asg, (.:=), (.::=), simassign
, i_skip, v_skip, skip, g_skip
, utpWC_Conjs, utpWC_Name, utpWC_Theory
, utpWC_Aliases
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
import StdTypeSignature
import UTP.Reading
import UTP.Observations
import UTP.Base
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we define the the ``While'' language,
which is a simple turing-complete imperative language.
We define six signature items: 
all program variables (\m{O},\m{O'},\m{O_m}),
seq-comp (\m{;}), 
conditionals (\m{\cond{\_}}), 
iteration (\m{\circledast}),
assignment (\m{:=}),
and 
skip (\m{\Skip}).
We also provide semantics for seq-comp, conditionals, and iteration,
which do not change across most variants.

\section{UTP While Signatures}

\subsection{Set of all program variables}

We also need to ensure that $O$, $O'$, and $O_m$ are ``known'',
but here they are \emph{abstract}:
\begin{code}
obsIntro = mkAbsSetVar vO
\end{code}
We need to be able to make use of the following properties in proofs:
$$
  O \cup O' \supseteq P \qquad O \cup O' \supseteq Q \qquad \dots
$$


\subsection{Conditionals}
$$ P \cond b Q $$
\begin{code}
cond :: Term -> Term -> Term -> Term
i_cond       =  jId "cond"
cond p b q   =  Cons arbpred True i_cond [p, b, q]
condIntro = mkConsIntro i_cond boolf_3
\end{code}

\subsection{Sequential Composition}
$$ P \seq Q $$
\begin{code}
mkSeq :: Term -> Term -> Term
i_seq        =  jId ";"
mkSeq p q    =  Cons arbpred False i_seq [p, q]
seqIntro = mkConsIntro i_seq boolf_2
\end{code}

\subsection{While Loop}
$$ c \circledast P$$
\begin{code}
while :: Term -> Term -> Term
i_while = jId "while"
while c p = Cons arbpred False i_while [c, p]
\end{code}

\subsection{(Simultaneous) Assignement}
$$ \lst x := \lst e $$
\begin{code}
listwiseVarBinPred :: Type -> Identifier -> Identifier
                    -> [(Variable,Variable)] -> [(ListVar,ListVar)] -> Term
listwiseVarBinPred tk na ni vvs lvlvs
  | null vvs    =  doiter lvlvs
  | null lvlvs  =  docons vvs
  | otherwise   =  Cons tk True na [docons vvs,doiter lvlvs]
  where
    docons [vv]       =  mkcons vv
    docons vvs        =  Cons tk True na $ map mkcons vvs
    mkcons (v1,v2)    =  Cons tk True ni [varAsTerm v1,varAsTerm v2]
    doiter [lvlv]     =  mkiter lvlv
    doiter lvlvs      =  Cons tk True na $ map mkiter lvlvs
    mkiter (lv1,lv2)  =  Iter tk True na True ni [lv1,lv2]


p1 = arbpred
i_asg        =  assignmentId
p_asg        =  jVar p1 $ Vbl i_asg PredV Textual

simassign :: [(Variable,Term)] -> [(ListVar,ListVar)] -> Term
simassign vts lvlvs  =  Sub p1 p_asg $ jSubstn vts lvlvs

(.:=) :: Variable -> Term -> Term
v .:= e      =  simassign [(v,e)] []

(.::=) :: ListVar -> ListVar -> Term
lv .::= le   =  simassign [] [(lv,le)]

asgIntro = mkConsIntro i_asg apred11
\end{code}

\subsection{Skip}
$$ \Skip $$
\begin{code}
skip :: Term
i_skip  =  jId "II"
v_skip  =  Vbl i_skip PredV Static
g_skip  =  StdVar v_skip
skip    =  jVar p1 v_skip 
\end{code}


\section{UTP While Semantics}





\subsection{UTP Conditionals}

\subsubsection{Defn. of Conditional}

From \cite[Defn 2.1.1,p47]{UTP-book}
$$
  \begin{array}{lll}
     P \cond b Q ~\defs~ (b \land P) \lor (\lnot b \land Q) &
     & \QNAME{$\cond\_$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
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


\subsection{UTP Sequential Composition}

\subsubsection{Defn. Sequential Composition}

From \cite[Defn 2.2.1,p49]{UTP-book}

$$
  \begin{array}{lll}
     P \seq Q ~\defs~ \exists O_0 \bullet P[O_0/O'] \land Q[O_0/O]
     & O,O'\supseteq_a P,Q ~~ O_0 \textrm{ fresh}
     & \QNAME{$;$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(axSeqDef,alSeqDef) = bookdef ("sqcmp" -.- "def") "Def2.2.1"
                       ( mkSeq p q
                         === exists [gO0]
                              ( (Sub pred1 p o0'sub) /\ (Sub pred1 q o0sub) )
                       )
                       (isUTPDynObs gp .: isUTPDynObs gq .: gfresh)
   where
      gfresh = fresh $ S.singleton gO0
\end{code}
We want to assert $O \supseteq P$, and rely on unformity to get the rest.


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
(cjSeqAssoc,alSeqAssoc) = bookdef ("sqcmp" -.- "assoc") "2.2L1"
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
(cjSeqLDistr,alSeqLDistr) = bookdef ("sqcmp" -.- "cond" -.- "l" -.- "distr") "2.2L2"
                              ( mkSeq (cond p b q) r
                                ===
                                cond (mkSeq p r) b (mkSeq q r)
                              )
                              (areUTPDynObs [gP,gQ,gR] .: isUTPCond gb)
\end{code}


\section{UTP Non-deterministic Choice}

Here we have laws involving n.d.c. and some While operators.

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
   = bookdef ("sqcmp" -.- "sqcap" -.- "ldistr") "2.4L6"
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
   = bookdef ("sqcmp" -.- "sqcap" -.- "rdistr") "2.4L7"
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

\textbf{THIS DOES NOT BELONG HERE}

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
utpWC_Knowns
 = condIntro $
   seqIntro $
   obsIntro $
   asgIntro $
   newNamedVarTable utpWC_Name
\end{code}


We now collect our axiom set:
\begin{code}
utpWC_Axioms :: [Law]
utpWC_Axioms
  = map labelAsAxiom
      [ axCondDef
      , axSeqDef
      , axFusionDef
     ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpWC_Conjs :: [NmdAssertion]
utpWC_Conjs
  = [ cjCondL1, cjCondL2, cjCondL3, cjCondL4, cjCondL5a
    , cjCondL5b, cjCondL6, cjCondL7, cjCondMutual, cjCondAlt, cjCondAlt2
    , cjSeqAssoc, cjSeqLDistr
    , cjCondNDCDistr, cjSeqNDCLDistr, cjSeqNDCRDistr, cjNDCCondDistr
    ]
\end{code}


We now collect our alias set:
\begin{code}
utpWC_Aliases :: [(String,String)]
utpWC_Aliases
  = [ alCondL1, alCondL2, alCondL3, alCondL4
    , alCondL5a, alCondL5b, alCondL6, alCondL7
    , alCondMutual
    , alSeqDef, alSeqAssoc, alSeqLDistr
    , alCondNDCDistr, alSeqNDCLDistr, alSeqNDCRDistr, alNDCCondDistr
    ]
\end{code}


\begin{code}
utpWC_Name :: String
utpWC_Name = "UWhile"
utpWC_Theory :: Theory
utpWC_Theory
  =  nullTheory { thName  =  utpWC_Name
                , thDeps  = [ utpBase_Name
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
            , known   =  utpWC_Knowns
            , laws    =  utpWC_Axioms
            , conjs   =  utpWC_Conjs
            }
\end{code}

\section{UTP While Infrastructure}

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
