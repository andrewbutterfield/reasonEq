\chapter{UTP Na\"{i}ve While}
\begin{verbatim}
Copyright  Andrew Butterfield, Danny Thomas (c) 2019--2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.NaiveWhile (
  utpNW_Conjs, utpNW_Name, utpNW_Theory
, utpNW_Aliases
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
import UTP.WhileRefineSig
import UTP.Observations
import UTP.CommonWhile

import TestRendering

import Debugger
\end{code}


\section{Introduction}


Here we provide semantics for the elements of the Na\"{i}"ve While theory,
were it differ from the corresponding Design semantics.

This only affects assignment and skip.


\section{UTP Assignment}

\subsection{Defn. of Assignment}

From \cite[Defn 2.3.1,p50]{UTP-book}

We start by defining simultaneous assignment,
based loosely on \cite[2.3\textbf{L2}, p50]{UTP-book}.
$$
  \begin{array}{lll}
     \lst x := \lst e
     ~\defs~
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



\subsection{UTP Assignment Laws}



\newpage
The following (\cite[Defn 2.3.1,p50]{UTP-book}) is now a conjecture:
$$
  \begin{array}{lll}
     x := e
     ~\defs~
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
  = bookdef (":=" -.- "seq" -.- "cond") "2.3L4"
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
skipIntro = mkKnownVar v_skip bool
(axSkipDef,alSkipDef) 
  = bookdef ("II" -.- "def") "Def2.3.2"
      ( skip  ===  Iter arbpred True land True equals [ lO', lO ] )
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
(cjSkipL5a,alSkipL5a) = bookdef (";" -.- "runit") "2.3L5a"
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
(cjSkipL5b,alSkipL5b) = bookdef (";" -.- "lunit") "2.3L5b"
                         (mkSeq skip r === r)
                         (areUTPDynObs [gR,g_skip])
\end{code}




\newpage
\section{UTP Na\"{i}ve" Theory}

We collect our known variables:
\begin{code}
utpNW_Known
 = asgIntro $
   skipIntro $
   newNamedVarTable utpNW_Name
\end{code}


We now collect our axiom set:
\begin{code}
utpNW_Axioms :: [Law]
utpNW_Axioms
  = map labelAsAxiom
      [ axAsgDef
      , axSkipDef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpNW_Conjs :: [NmdAssertion]
utpNW_Conjs
  = [ cjAsgSimple, cjAsgUnchanged, cjAsgSeqSame, cjAsgSeqCond
    , cjSkipL5a, cjSkipL5b
    ]
\end{code}


We now collect our alias set:
\begin{code}
utpNW_Aliases :: [(String,String)]
utpNW_Aliases
  = [ alAsgDef, alAsgUnchanged, alAsgSeqSame, alAsgSeqCond
    , alSkipDef, alSkipL5a, alSkipL5b
    ]
\end{code}


\begin{code}
utpNW_Name :: String
utpNW_Name = "U_NvWhl"
utpNW_Theory :: Theory
utpNW_Theory
  =  nullTheory { thName  =  utpNW_Name
                , thDeps  = [ utpCW_Name
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
            , known   =  utpNW_Known
            , laws    =  utpNW_Axioms
            , conjs   =  utpNW_Conjs
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
