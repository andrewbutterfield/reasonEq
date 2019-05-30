\section{XYZ Theory}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

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
-- for use in expressions
e = fromJust $ eVar int ve
f = fromJust $ eVar int vf
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

\begin{code}
xyzKnown  =   fromJust $ addKnownVar vx  int
            $ fromJust $ addKnownVar vy  int
            $ fromJust $ addKnownVar vz  int
            $ fromJust $ addKnownVar vx' int
            $ fromJust $ addKnownVar vy' int
            $ fromJust $ addKnownVar vz' int
            $ newVarTable
\end{code}

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
\end{code}


We now collect our axiom set:
\begin{code}
xyzAxioms :: [Law]
xyzAxioms
  = map labelAsAxiom
      [ axXYZSeqDef, axSeqDef
      , axXAsgDef, axYAsgDef, axZAsgDef
      ]
\end{code}



\subsection{XYZ Conjectures}


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
  = [  ]
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
