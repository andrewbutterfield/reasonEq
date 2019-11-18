\section{UTP Start-up}
\begin{verbatim}
Copyright  Andrew Buttefield, Danny Thomas (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPStartup (
  univ
, utpStartupConjs, utpStartupName, utpStartupTheory
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
import PropSubst
import Equivalence
import PropNot
import PropDisj
import PropConj
import PropMixOne
import PropImpl
import Equality
import PredAxioms
import PredExists
import PredUniv
import TestRendering
\end{code}


\newpage
\subsection{Introduction}


This builtin theory is being used to prototype the building of UTP
support of top of the propostional and predicate foundation already done.


\subsection{Predicate Infrastructure}

Most variables have an ``underlying'' definition
that is then ``wrapped'' in different ways depending on where it is used.

$$P \quad Q \quad R$$
\begin{code}
-- underying variable
vp = Vbl (fromJust $ ident "P") PredV Static
p = fromJust $ pVar vp
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
-- for use in side-conditions
gvP = StdVar vp
\end{code}


$$ b \quad b' \qquad c  \quad c' $$
\begin{code}
b  = fromJust $ pVar $ Vbl (fromJust $ ident "b") PredV Before
b' = fromJust $ pVar $ Vbl (fromJust $ ident "b") PredV After
c  = fromJust $ pVar $ Vbl (fromJust $ ident "c") PredV Before
c' = fromJust $ pVar $ Vbl (fromJust $ ident "c") PredV After
\end{code}


$$ v \qquad \lst v $$
\begin{code}
(v,vs) = (StdVar vv, LstVar lvvs)
  where
   vv   = Vbl (fromJust $ ident "v") ObsV Static
   lvvs = LVbl vv [] []
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

For use in expressions  and substitution first list
\\(e.g. $x+y$ might be \texttt{plus [x,y]}):
\begin{code}
[x,y,z,x',y',z'] = map (fromJust . eVar int) [vx,vy,vz,vx',vy',vz']
\end{code}

For use in quantifier variable list/sets and substitution second lists
\\(e.g. $\forall x,x' \bullet P$ would be \texttt{forall [qx,qx'] p}):
\begin{code}
[qx,qy,qz,qx',qy',qz'] = map StdVar [vx,vy,vz,vx',vy',vz']
\end{code}

$$ x_m \qquad y_m \qquad z_m$$
For use in quantifier variable list/sets and substitutions:
\begin{code}
xm = StdVar $ Vbl (fromJust $ ident "x") ObsV (During "m")
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
sub p = Sub P p $ fromJust $ substn [(vx,e)] []
lvxs = LVbl vx [] []
qxs = LstVar lvxs
lsub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}


\newpage
\subsection{UTP-Startup Axioms}

\subsubsection{Axiom 1}
$$
  \begin{array}{lll}
     P \cond b Q \defs P \land b \lor Q \land \not b &
     & \QNAME{UTP-ax-001}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
mkCond p b q = PCons(fromJust $ ident "cond")[p, b, q]

mkSeq p q = PCons (fromJust $ ident ";")[p, q]


axUTP001 = preddef ("UTP" -.- "ax" -.- "001")
                    (mkCond p b q === (p /\ b) \/ (q /\ mkNot b))
                    scTrue
\end{code}


\subsection{UTP-Startup Conjectures}

%\subsubsection{Conjecture 1}
$$
  \begin{array}{lll}
     P \cond b Q \equiv (b \implies P) \land (\lnot b \implies Q)
     && \QNAME{UTP-cj-001}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjUTPdef = preddef ("UTP" -.- "cj" -.- "alt" -.- "def")
                     (mkCond p b q === (b ==> p) /\ (mkNot b ==> q))
                     scTrue
\end{code}

\begin{code}
cjUTPdef2 = preddef ("UTP" -.- "cj" -.- "alt" -.- "def2")
                     (mkCond p b q === ((mkNot b \/ p) === (b \/ q)))
                     scTrue
\end{code}

\begin{code}
cjUTPL1 = preddef ("UTP" -.- "cj" -.- "L1")
                     (mkCond p b p === p)
                     scTrue
\end{code}

\begin{code}
cjUTPL2 = preddef ("UTP" -.- "cj" -.- "L2")
                     (mkCond p b q === mkCond q (mkNot b) p)
                     scTrue
\end{code}

\begin{code}
cjUTPL3 = preddef ("UTP" -.- "cj" -.- "L3")
                  ( mkCond (mkCond p b q) c r
                    ===
                    mkCond p (b /\ c) (mkCond q c r) )
                  scTrue
\end{code}

\begin{code}
cjUTPL4 = preddef ("UTP" -.- "cj" -.- "L4")
                  ( mkCond p b (mkCond q c r)
                    ===
                    mkCond (mkCond p b q) c (mkCond p b r) )
                  scTrue
\end{code}

\begin{code}
cjUTPL5a = preddef ("UTP" -.- "cj" -.- "L5a")
                     (mkCond p trueP q === p)
                     scTrue
\end{code}

\begin{code}
cjUTPL5b = preddef ("UTP" -.- "cj" -.- "L5b")
                      (mkCond p falseP q === q)
                      scTrue
\end{code}

\begin{code}
cjUTPL6 = preddef ("UTP" -.- "cj" -.- "L6")
                     (mkCond p b (mkCond q b r) === mkCond p b r)
                     scTrue
\end{code}

\begin{code}
cjUTPL7 = preddef ("UTP" -.- "cj" -.- "L7")
                    (mkCond p b (mkCond p c q) === mkCond p (b \/ c) q)
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

We now collect our axiom set:
\begin{code}
utpStartupAxioms :: [Law]
utpStartupAxioms
  = map labelAsAxiom
      [ axUTP001 ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpStartupConjs :: [NmdAssertion]
utpStartupConjs
  = [ cjUTPdef,
      cjUTPdef2,
      cjUTPL1,
      cjUTPL2,
      cjUTPL3,
      cjUTPL4,
      cjUTPL5a,
      cjUTPL5b,
      cjUTPL6,
      cjUTPL7 ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
utpStartupName :: String
utpStartupName = "UTPStartup"
utpStartupTheory :: Theory
utpStartupTheory
  =  Theory { thName  =  utpStartupName
            , thDeps  =  [ predUnivName
                         , predExistsName
                         , predAxiomName
                         , equalityName
                         , propSubstName
                         , propImplName
                         , propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , equivName
                         ]
            , known   =  newVarTable
            , laws    =  utpStartupAxioms
            , proofs  =  []
            , conjs   =  utpStartupConjs
            }
\end{code}
