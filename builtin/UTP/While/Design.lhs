\chapter{UTP While Design}
\begin{verbatim}
Copyright  Andrew Butterfield, Danny Thomas (c) 2019--2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.While.Design (
  i_asg, (.:=), (.::=), simassign
, utpWD_Conjs, utpWD_Name, utpWD_Theory
, utpWD_Aliases
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
import Closure
import StdTypeSignature
import UTP.Reading
import UTP.Observations
import UTP.Base
import UTP.While.Common
import UTP.Designs

import TestRendering

import Debugger
\end{code}


\section{Introduction}


Here we provide a Design semantics for the While language.
This requires a design-specific  semantics for both assignment and skip.

\textbf{EVERYTHING BELOW IS FROM CHAPTER 2 AND IS PRE-DESIGN}

\section{While-Design Signature}

\section{UTP Assignment}


\begin{code}
p1 = arbpred
i_asg        =  assignmentId
p_asg        =  jVar p1 $ Vbl i_asg PredV Static

simassign :: [(Variable,Term)] -> [(ListVar,ListVar)] -> Term
simassign vts lvlvs  =  Sub p1 p_asg $ xSubstn vts lvlvs

(.:=) :: Variable -> Term -> Term
v .:= e      =  simassign [(v,e)] []

(.::=) :: ListVar -> ListVar -> Term
lv .::= le   =  simassign [] [(lv,le)]

asgIntro = mkConsIntro i_asg apred11 False
\end{code}

\subsection{Defn. of Assignment}

From \cite[Defn 2.3.1,p50]{UTP-book}

We start by defining simultaneous assignment,
based loosely on \cite[2.3\textbf{L2}, p50, and Def 3.1.3, p78]{UTP-book}
$$
  \begin{array}{lll}
     \lst x := \lst e
     ~\defs~
     \true \design
     \lst x' = \lst e \land O'\less {ok,\lst x} = O \less {ok,\lst x}
     && \QNAME{$:=$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(axAsgDef,alAsgDef) = bookdef ("asg" -.- "def") "Def3.1.3p78"
                       ( lvxs .::= lves
                         ===
                         ( trueP
                           `design`
                           ( (lvx' `areEqualTo` lves)
                             /\
                             ( (lO' `less` ([ok],[ix]))
                               `areEqualTo`
                               (lO  `less` ([ok],[ix])) ) ) )
                       )
                       scTrue
\end{code}



\subsection{UTP Assignment Laws}



\newpage
The following (\cite[Defn 3.1.3, p78]{UTP-book}) is now a conjecture:
$$
  \begin{array}{lll}
     x := e
     ~\defs~
     (\true \design x' = e \land O'\less{ok,x} = O \less{ok,x})
     && \QNAME{$:=$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjAsgSimple,alAsgSimple) = bookdef ("asg" -.- "simple") "Def2.3.1"
                       ( vx .:= e
                         ===
                         ( trueP 
                           `design`
                           ( (x' `isEqualTo` e)
                           /\
                           ( (lO' `less` ([ok,ix],[]))
                             `areEqualTo`
                           (lO  `less` ([ok,ix],[])) ) ) ) )
                       scTrue
\end{code}

Adapted for designs from \cite[2.3\textbf{L1}, p50]{UTP-book}
$$
  \begin{array}{lll}
     x := e  =  (x,y := e,y)
     && \QNAME{$:=$-unchanged}
  \\ = x' = e \land y' = y \land O'\less {\lst x,\lst y} = O \less {\lst x, \lst y}
  \end{array}
$$
\begin{code}
(cjAsgUnchanged,alAsgUnchanged)
  = bookdef ("asg" -.- "unchanged") "2.3L3"
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
  = bookdef ("asg" -.- "seq" -.- "same") "2.3L3"
     ( mkSeq (vx .:= e) (vx .:= f)
       ===
       ( vx .:= Sub ArbType f e_for_x )
     )
     (areUTPCond [gx,qe,qf])
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
  = bookdef ("asg" -.- "seq" -.- "cond") "2.3L4"
     ( mkSeq (vx .:= e) (cond p b q)
       ===
       ( cond (mkSeq (vx .:= e) p)
              (Sub ArbType b e_for_x)
              (mkSeq (vx .:= e) q) )
     )
     (areUTPDynObs [gP,gQ] .: areUTPCond [gx,qe,gb])
\end{code}

\newpage
\section{UTP ``Skip''}

\subsection{Defn. of Skip}

From \cite[Defn 2.3.2,p50]{UTP-book}

$$
  \begin{array}{lll}
     \Skip ~\defs~ O' = O
     && \QNAME{$\Skip$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(axSkipDef,alSkipDef) 
  = bookdef ("II" -.- "def") "Def3.1.3 L3 p79"
      ( skip  ===  ( trueP
                     `design`
                     ( Iter arbpred True land True equals 
                      [ lO' `less` ([ok],[]), lO `less` ([ok],[])] ) )
      )
      scTrue
\end{code}

\subsection{UTP Skip Laws}

From \cite[2.3\textbf{L5}, p50]{UTP-book}
$$
  \begin{array}{lll}
     R \seq \Skip \equiv R   & O,O'\supseteq R
     & \QNAME{$;$-runit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSkipL5a,alSkipL5a) = bookdef ("sqcmp" -.- "runit") "2.3L5a"
                         (mkSeq r skip === r)
                         (areUTPDynObs [gR,g_skip])
\end{code}

From \cite[2.3\textbf{L5}, p50]{UTP-book}
$$
  \begin{array}{lll}
     \Skip \seq R \equiv R   & O,O'\supseteq R
     & \QNAME{$;$-lunit}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjSkipL5b,alSkipL5b) = bookdef ("sqcmp" -.- "lunit") "2.3L5b"
                         (mkSeq skip r === r)
                         (areUTPDynObs [gR,g_skip])
\end{code}


\newpage
\section{UTP Abort}

\subsection{Defn. of Abort}

From \cite[Theorem 3.1.5, p80]{UTP-book}

$$
  \begin{array}{lll}
     \bot  = \false \design \true
     && \QNAME{$\bot$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(axAbortDef,alAbortDef) = bookdef ("bot" -.- "def") "Thm3.1.5 p80"
                           ( abort  ===  falseP `design` trueP )
                           scTrue
\end{code}

$$
  \begin{array}{lll}
     \bot  = \true
     && \QNAME{$\bot$-is-$\true$}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjAbortTrue,alAbortTrue) = bookdef ("bot" -.- "true") "Thm3.1.5 p80"
                           ( abort  ===  trueP )
                           scTrue
\end{code}

\section{UTP Miracle}

\subsection{Defn. of Miracle}

From \cite[Theorem 3.1.5, p80]{UTP-book}

$$
  \begin{array}{lll}
     \top  = \true \design \false
     && \QNAME{$\top$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(axMiracleDef,alMiracleDef) = bookdef ("top" -.- "def") "Thm3.1.5 p80"
                           ( miracle  ===  trueP `design` falseP )
                           scTrue
\end{code}

$$
  \begin{array}{lll}
     \top  = \true \design \false
     && \QNAME{$\top$-is-not-$ok$}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjMiracleNOK,alMiracleNOK) = bookdef ("top" -.- "nok") "Thm3.1.5 p80"
                           ( miracle  ===  mkNot tok )
                           scTrue
\end{code}


\newpage
\section{UTP While Design}

All known variables are declared in imported theories.
\begin{code}
utpWD_Knowns
 =    asgIntro $
      newNamedVarTable utpWD_Name
\end{code}


We now collect our axiom set:
\begin{code}
utpWD_Axioms :: [Law]
utpWD_Axioms
  = map labelAsAxiom
      [ axAsgDef, axFusionDef
      , axSkipDef
      , axAbortDef
      , axMiracleDef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpWD_Conjs :: [NmdAssertion]
utpWD_Conjs
  = [ cjAsgSimple, cjAsgUnchanged, cjAsgSeqSame, cjAsgSeqCond
    , cjSkipL5a, cjSkipL5b
    , cjAbortTrue
    , cjMiracleNOK
    ]
\end{code}


We now collect our alias set:
\begin{code}
utpWD_Aliases :: [(String,String)]
utpWD_Aliases
  = [ alAsgDef, alAsgUnchanged, alAsgSeqSame, alAsgSeqCond
    , alSkipDef, alSkipL5a, alSkipL5b
    , alAbortDef, alMiracleDef
    ]
\end{code}


\begin{code}
utpWD_Name :: String
utpWD_Name = "DWhile"
utpWD_Theory :: Theory
utpWD_Theory
  =  nullTheory { thName  =  utpWD_Name
                , thDeps  = [ designName
                            , utpWC_Name
                            , utpBase_Name
                            , closureName
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
            , known   =  utpWD_Knowns
            , laws    =  utpWD_Axioms
            , conjs   =  utpWD_Conjs
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

\section{Design Foundations and Concepts}


To be distributed above as appropriate

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


\section{Variable List Fusion}

\textbf{Is associated with assignment!!!}

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


\section{Chapter 3 STUFF}

For now we just list definitions and theorems in Chp 3.
Some regarding assignment and skip should end up in \h{UTP.While.Design}

From \cite[p79]{UTP-book} (modified):
$$
  \Skip ~~\defs~~ (\true \design S'=S)
$$





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