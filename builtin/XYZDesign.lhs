\section{XYZ Design Theory}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module XYZDesign (
  univ
, xyzDConjs, xyzDName, xyzDTheory
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
import PredUniv
import UTPStartup
import TestRendering
\end{code}


\newpage
\subsection{Introduction}


This builtin theory defines the alphabet,
sequential composition, and assignments
for a UTP theory of total correctness
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
\end{code}


$$ x \quad y \quad z \quad ok \qquad x' \quad y' \quad z' \quad ok'$$

Underlying identifiers:
\begin{code}
ix  = fromJust $ ident "x"
iy  = fromJust $ ident "y"
iz  = fromJust $ ident "z"
iok = fromJust $ ident "ok"
\end{code}
Underlying variables:
\begin{code}
vx  = Vbl ix ObsV Before
vy  = Vbl iy ObsV Before
vz  = Vbl iz ObsV Before
vx' = Vbl ix ObsV After
vy' = Vbl iy ObsV After
vz' = Vbl iz ObsV After
vok = Vbl iok ObsV Before
vok' = Vbl iok ObsV After
\end{code}


% For use in quantifier variable list/sets and substitution second lists
% \\(e.g. $\forall x,x' \bullet P$ would be \texttt{forall [qx,qx'] p}):
% \begin{code}
% [qx,qy,qz,qx',qy',qz'] = map StdVar [vx,vy,vz,vx',vy',vz']
% \end{code}

$$ x_m \qquad y_m \qquad z_m \qquad okm$$
For use in quantifier variable list/sets and substitutions:
\begin{code}
vxm = Vbl ix ObsV (During "m")
vym = Vbl iy ObsV (During "m")
vzm = Vbl iz ObsV (During "m")
vokm = Vbl iok ObsV (During "m")
\end{code}

For use in expressions and substitution first list replacements
\\(e.g. $x+y$ might be \texttt{plus [x,y]}):
\begin{code}
[x,y,z,ok,x',y',z',ok',xm,ym,zm,okm]
  = map (fromJust . eVar int) [vx,vy,vz,vok,vx',vy',vz',vok',vxm,vym,vzm,vokm]
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
-- for use in expressions
e = fromJust $ eVar int ve
f = fromJust $ eVar int vf
-- for use in quantifiers, substitutions (first list)
qe = StdVar ve
qf = StdVar vf
qxm = StdVar vxm ; qym = StdVar vym ; qzm = StdVar vzm; qokm = StdVar vokm
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

The alphabet for this theory is $\setof{x,y,z,ok,x',y',z',ok'}$.

We also have a known predicate variable $\Skip$,
defined to be $ok \implies ok' \land x'=x \land y'=y \land z'=z$.

\begin{code}
skip = Vbl (fromJust $ ident "II") PredV Static
skipDef =
  ok ==> ok' /\ ( x' `isEqualTo` x /\ ( y' `isEqualTo` y /\ z' `isEqualTo` z) )

xyzDKnown  =   fromJust $ addKnownConst skip skipDef
            $ fromJust $ addKnownVar vx  int
            $ fromJust $ addKnownVar vy  int
            $ fromJust $ addKnownVar vz  int
            $ fromJust $ addKnownVar vx' int
            $ fromJust $ addKnownVar vy' int
            $ fromJust $ addKnownVar vz' int
            $ fromJust $ addKnownVar vok int
            $ fromJust $ addKnownVar vok' int
            $ newVarTable
\end{code}

\newpage
\subsection{XYZ Design Axioms}

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
before r = Sub P r $ fromJust $ substn [(vx',xm),(vy',ym),(vz',zm),(vok',okm)] []
after r  = Sub P r $ fromJust $ substn [(vx,xm), (vy,ym), (vz,zm),(vok,okm)] []

axXYZSeqDef = preddef ("XYZD" -.- ";" -.- "def")
                   ( mkSeq p q
                     ===
                     exists [qxm,qym,qzm,qokm]
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

\subsubsection{Design}

$$
  \begin{array}{lll}
     P \vdash Q \defs ok \land P \implies ok' \land Q && \QNAME{$\vdash$-Def}
  \end{array}
$$\par%\vspace{-8pt}
\begin{code}
mkDesign p q = PCons (fromJust $ ident "vdash") [p,q]

axDesignDef = preddef ("vdash" -.- "def")
                   ( mkDesign p q
                     ===
                     ok /\ p ==> ok' /\ q )
                    scTrue
\end{code}

\newpage
\subsubsection{Assignment}


$$
  \begin{array}{lll}
     x := e \defs (\true \vdash x' = e \land y' = y \land z' = z)
     && \QNAME{X-$:=$-def}
  \\ y := e \defs (\true \vdash x' = x \land y' = e \land z' = z)
     && \QNAME{Y-$:=$-def}
  \\ z := e \defs (\true \vdash x' = x \land y' = y \land z' = e)
      && \QNAME{Z-$:=$-def}
  \\
  \end{array}
$$\par%\vspace{-8pt}
\begin{code}
mkAsg x e = PCons (fromJust $ ident ":=")[x, e]
preT p = mkDesign trueP p

axdXAsgDef = preddef ("X" -.- ":=" -.- "def")
                   ( mkAsg x e
                     ===
                     preT (x' `isEqualTo` e /\
                     ( y' `isEqualTo` y /\ z' `isEqualTo` z)  ) )
                    scTrue
axdYAsgDef = preddef ("Y" -.- ":=" -.- "def")
                   ( mkAsg y e
                     ===
                     preT (x' `isEqualTo` x /\
                     ( y' `isEqualTo` e /\ z' `isEqualTo` z)  ) )
                    scTrue
axdZAsgDef = preddef ("Z" -.- ":=" -.- "def")
                   ( mkAsg z e
                     ===
                     preT (x' `isEqualTo` x /\
                     ( y' `isEqualTo` y /\ z' `isEqualTo` e)  ) )
                    scTrue
\end{code}


We now collect our axiom set:
\begin{code}
xyzDAxioms :: [Law]
xyzDAxioms
  = map labelAsAxiom
      [ axXYZSeqDef, axSeqDef
      , axDesignDef
      , axdXAsgDef, axdYAsgDef, axdZAsgDef
      ]
\end{code}



\subsection{XYZ Design Conjectures}


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
xyzDConjs :: [NmdAssertion]
xyzDConjs
  = [  ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
xyzDName :: String
xyzDName = "XYZDesign"
xyzDTheory :: Theory
xyzDTheory
  =  Theory { thName  =  xyzDName
            , thDeps  =  [ utpStartupName
                         , predUnivName
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
            , known   =  xyzDKnown
            , laws    =  xyzDAxioms
            , proofs  =  [] --
            , conjs   =  xyzDConjs
            }
\end{code}
