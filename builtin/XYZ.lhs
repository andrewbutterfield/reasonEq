\section{XYZ Theory}
\begin{verbatim}
Copyright  Andrew Buttefield, Danny Thomas (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module XYZ (
  univ
, xyzConjs, xyzName, xyzTheory
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

import PropAxioms
import PropSubst
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropMixOne
import PropImpl
import Equality
import PredAxioms
import PredExists
import PredUniv
import UTPStartup
import TestRendering
\end{code}


\newpage
\subsection{Introduction}


This builtin theory defines the alphabet,
sequential composition, and assignments
for a UTP theory of partial correctness
for a programming language with three variables: $x$, $y$, and $z$.


\subsection{Predicate Infrastructure}

Most variables have an ``underlying'' definition
that is then ``wrapped'' in different ways depending on where it is used.

$$P \qquad Q$$
\begin{code}
-- underlying variable
vp = Vbl (fromJust $ ident "P") PredV Static
p = fromJust $ pVar vp
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static

b  = fromJust $ pVar $ Vbl (fromJust $ ident "b") PredV Before
b' = fromJust $ pVar $ Vbl (fromJust $ ident "b") PredV After
c  = fromJust $ pVar $ Vbl (fromJust $ ident "c") PredV Before
c' = fromJust $ pVar $ Vbl (fromJust $ ident "c") PredV After

\end{code}


$$ x \quad y \quad z \qquad x' \quad y' \quad z'$$

Underlying variables:
\begin{code}
vx  = Vbl (fromJust $ ident "x") ObsV Before
vy  = Vbl (fromJust $ ident "y") ObsV Before
vz  = Vbl (fromJust $ ident "z") ObsV Before
vx' = Vbl (fromJust $ ident "x") ObsV After
vy' = Vbl (fromJust $ ident "y") ObsV After
vz' = Vbl (fromJust $ ident "z") ObsV After
\end{code}


%zero = Vbl (fromJust $ ident "zero") ObsV Static


% For use in quantifier variable list/sets and substitution second lists
% \\(e.g. $\forall x,x' \bullet P$ would be \texttt{forall [qx,qx'] p}):
% \begin{code}
% [qx,qy,qz,qx',qy',qz'] = map StdVar [vx,vy,vz,vx',vy',vz']
% \end{code}

$$ x_m \qquad y_m \qquad z_m$$
For use in quantifier variable list/sets and substitutions:
\begin{code}
vxm = Vbl (fromJust $ ident "x") ObsV (During "m")
vym = Vbl (fromJust $ ident "y") ObsV (During "m")
vzm = Vbl (fromJust $ ident "z") ObsV (During "m")
\end{code}

For use in expressions and substitution first list replacements
\\(e.g. $x+y$ might be \texttt{plus [x,y]}):
\begin{code}
[x,y,z,x',y',z',xm,ym,zm]
  = map (fromJust . eVar int) [vx,vy,vz,vx',vy',vz',vxm,vym,vzm]
\end{code}

$$\Nat \qquad \Int$$
\begin{code}
nat  = GivenType $ fromJust $ ident $ _mathbb "N"
int  = GivenType $ fromJust $ ident $ _mathbb "Z"
\end{code}

$$ e \quad \lst e  \qquad f \quad \lst f$$
\begin{code}
-- Underlying variables:
ve = Vbl (fromJust $ ident "e") ExprV Before
vf = Vbl (fromJust $ ident "f") ExprV Before
vg = Vbl (fromJust $ ident "g") ExprV Before
-- for use in expressions
e = fromJust $ eVar int ve
f = fromJust $ eVar int vf
g = fromJust $ eVar int vg
-- for use in quantifiers, substitutions (first list)
qe = StdVar ve
qf = StdVar vf
qxm = StdVar vxm ; qym = StdVar vym ; qzm = StdVar vzm
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
sub_x_by_e p = Sub P p $ fromJust $ substn [(vx,e)] []
sub_xs_by_es p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
lvxs = LVbl vx [] []
qxs = LstVar lvxs
\end{code}

\newpage
\subsection{XYZ alphabet}

The alphabet for this theory is $\setof{x,y,z,x',y',z'}$.

We also have a known predicate variable $\Skip$,
defined to be $x'=x \land y'=y \land z'=z$.

\begin{code}
skip = Vbl (fromJust $ ident "II") PredV Static
skipDef = x' `isEqualTo` x /\ ( y' `isEqualTo` y /\ z' `isEqualTo` z)


xyzKnown  =   fromJust $ addKnownConst skip skipDef
            $ fromJust $ addKnownVar vx  int
            $ fromJust $ addKnownVar vy  int
            $ fromJust $ addKnownVar vz  int
            $ fromJust $ addKnownVar vx' int
            $ fromJust $ addKnownVar vy' int
            $ fromJust $ addKnownVar vz' int
            $ newVarTable
\end{code}

%$ fromJust $ addKnownVar zero nat

\newpage
\subsection{XYZ Axioms}

\subsubsection{Sequential Composition}
$$
  \begin{array}{lll}
     P ; Q
     \defs
     \exists x_m,y_m,z_m \bullet
       P[x_m,y_m,z_m/x',y',z']
       \land
       Q[x_m,y_m,z_m/x,y,z]
     &
     & \QNAME{XYZ-;-Def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
mkSeq p q = PCons (fromJust $ ident ";")[p, q]

mkIn p q = PCons (fromJust $ ident "in")[p, q]

mkNat p = PCons (fromJust $ ident "Nat")[p]

mkSuc p = PCons (fromJust $ ident "S")[p]

mkZero = PCons (fromJust $ ident "Zer")[]

mkPlus p q = PCons (fromJust $ ident "+")[p, q]

before r = Sub P r $ fromJust $ substn [(vx',xm),(vy',ym),(vz',zm)] []
after r  = Sub P r $ fromJust $ substn [(vx,xm), (vy,ym), (vz,zm)] []

axXYZSeqDef = preddef ("XYZ" -.- ";" -.- "def")
                   ( mkSeq p q
                     ===
                     exists [qxm,qym,qzm]
                      (before p /\ after q)  )
                    scTrue
\end{code}

$$
  \begin{array}{lll}
     P ; Q
     \defs
     \exists O_m \bullet
       P[O_m/O']
       \land
       Q[O_m/O]
     &
     & \QNAME{XYZ-;-Def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
o   = fromJust $ ident "O"
lO  = PreVars o
lO' = PostVars o
lOm = MidVars o "m"

beforeO r = Sub P r $ fromJust $ substn [] [(lO',lOm)]
afterO r  = Sub P r $ fromJust $ substn [] [(lO,lOm)]

axSeqDef = preddef (";" -.- "def")
                   ( mkSeq p q
                     ===
                     exists [LstVar lOm]
                      (beforeO p /\ afterO q)  )
                    scTrue
\end{code}

\subsubsection{Assignment}

$$
  \begin{array}{lll}
     x := e \defs x' = e \land y' = y \land z' = z && \QNAME{X-$:=$-def}
  \\ y := e \defs x' = x \land y' = e \land z' = z && \QNAME{Y-$:=$-def}
  \\ z := e \defs x' = x \land y' = y \land z' = e && \QNAME{Z-$:=$-def}
  \\
  \end{array}
$$\par%\vspace{-8pt}
\begin{code}
mkAsg x e = PCons (fromJust $ ident ":=")[x, e]

mkCond p b q = PCons(fromJust $ ident "cond")[p, b, q]


axXAsgDef = preddef ("X" -.- ":=" -.- "def")
                   ( mkAsg x e
                     ===
                     x' `isEqualTo` e /\
                     ( y' `isEqualTo` y /\ z' `isEqualTo` z)  )
                    scTrue
axYAsgDef = preddef ("Y" -.- ":=" -.- "def")
                   ( mkAsg y e
                     ===
                     x' `isEqualTo` x /\
                     ( y' `isEqualTo` e /\ z' `isEqualTo` z)  )
                    scTrue
axZAsgDef = preddef ("Z" -.- ":=" -.- "def")
                   ( mkAsg z e
                     ===
                     x' `isEqualTo` x /\
                     ( y' `isEqualTo` y /\ z' `isEqualTo` e)  )
                    scTrue

axSeqCompL1 = preddef ("SeqComp" -.- "L1")
                   ( mkSeq (mkSeq p q) r === mkSeq p (mkSeq q r))
                   scTrue

axSeqCompL2 = preddef ("SeqComp" -.- "L2")
                  ( mkSeq (mkCond p b q) r === mkCond (mkSeq p r) b (mkSeq q r))
                   scTrue


axPeano01 = preddef ("Peano" -.- "01")
                  (mkNat mkZero)
                  scTrue

axPeano02 = preddef ("Peano" -.- "02")
                  (p `isEqualTo` p)
                  scTrue

axPeano03 = preddef ("Peano" -.- "03")
                  (q `isEqualTo` p === p `isEqualTo` q)
                  scTrue

axPeano04 = preddef ("Peano" -.- "04")
                  (p `isEqualTo` q /\ q `isEqualTo` r ==> p `isEqualTo` r)
                  scTrue

axPeano05 = preddef ("Peano" -.- "05")
                  (mkNat p /\ (p `isEqualTo` q) ==> mkNat q)
                  scTrue

axPeano06 = preddef ("Peano" -.- "06")
                  (mkNat p ==> mkNat (mkSuc p))
                  scTrue

axPeano07 = preddef ("Peano" -.- "07")
                  ((p `isEqualTo` q) === (mkSuc p `isEqualTo` mkSuc q))
                  scTrue

axPeano08 = preddef ("Peano" -.- "08")
                  ((mkZero === mkSuc p) === falseP)
                  scTrue

axPeano09 = preddef ("Peano" -.- "09")
                  (mkIn mkZero p /\ (mkIn q p ==> mkIn (mkSuc q) p) ==> p )
                  scTrue

axPeanoAdd01 = preddef ("Peano" -.- "Addition" -.- "1")
                  (mkPlus p mkZero === p)
                  scTrue

axPeanoAdd02 = preddef ("Peano" -.- "Addition" -.- "2")
                  (mkPlus p (mkSuc q) === mkSuc (mkPlus p q))
                  scTrue

axPeanoAdd03 = preddef ("Peano" -.- "Addition" -.- "3")
                  (mkPlus p q === mkPlus q p)
                  scTrue


\end{code}



We now collect our axiom set:
\begin{code}
xyzAxioms :: [Law]
xyzAxioms
  = map labelAsAxiom
      [ axXYZSeqDef, axSeqDef
      , axXAsgDef, axYAsgDef, axZAsgDef,
      axSeqCompL1, axSeqCompL2,
      axPeano01, axPeano02, axPeano03, axPeano04, axPeano05,
      axPeano06, axPeano07, axPeano08, axPeano09, axPeanoAdd01,
      axPeanoAdd02, axPeanoAdd03
      ]
\end{code}



\subsection{XYZ Conjectures}

\begin{code}
cjNonDeterL5 = preddef ("NonDeter" -.- "cj" -.- "L5")
                    (mkCond p b (q \/ r) === (mkCond p b q) \/ (mkCond p b r))
                    scTrue
\end{code}

\begin{code}

cjNonDeterL6 = preddef ("NonDeter" -.- "cj" -.- "L6")
                    (mkSeq (p \/ q) r === (mkSeq p r) \/ (mkSeq q r))
                    scTrue

\end{code}



\begin{code}

cjNonDeterL7 = preddef ("NonDeter" -.- "cj" -.- "L7")
                    (mkSeq p (q \/ r) === (mkSeq p q) \/ (mkSeq p r))
                    scTrue

\end{code}

\begin{code}

cjNonDeterL8 = preddef ("NonDeter" -.- "cj" -.- "L8")
                    (p \/ mkCond q b r === mkCond (p \/ q) b (p \/ r))
                    scTrue

\end{code}

\begin{code}

cjPeanoAdd03 = preddef ("Peano" -.- "Addition" -.- "3")
                  (mkPlus p (mkSuc mkZero) === mkSuc p)
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

We now collect our conjecture set:
\begin{code}
xyzConjs :: [NmdAssertion]
xyzConjs
  = [ cjNonDeterL5, cjNonDeterL6, cjNonDeterL7, cjNonDeterL8,
      cjPeanoAdd03 ]
\end{code}






\subsection{The Predicate Theory}

\begin{code}
xyzName :: String
xyzName = "XYZ"
xyzTheory :: Theory
xyzTheory
  =  Theory { thName  =  xyzName
            , thDeps  =  [ utpStartupName
                         , predUnivName
                         , predExistsName
                         , predAxiomName
                         , equalityName
                         , propSubstName
                         , propImplName
                         , propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName
                         ]
            , known   =  xyzKnown
            , laws    =  xyzAxioms
            , proofs  =  [] --
            , conjs   =  xyzConjs
            }
\end{code}
