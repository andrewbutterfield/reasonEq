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

\subsection{UTP Refinement}

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

\subsection{UTP Sequential Composition}

\subsection{UTP Assignment}

\subsection{UTP ``Skip''}

\subsection{UTP Non-deterministic Choice}

\subsection{UTP Base Theory}

We now collect our axiom set:
\begin{code}
utpBaseAxioms :: [Law]
utpBaseAxioms
  = map labelAsAxiom
      [ axCondDef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpBaseConjs :: [NmdAssertion]
utpBaseConjs
  = [ cjCondL1, cjCondL2, cjCondL3, cjCondL4, cjCondL5a
    , cjCondL5b, cjCondL6, cjCondL7, cjCondAlt, cjCondAlt2
    ]
\end{code}

We now collect our alias set:
\begin{code}
utpBaseAliases :: [(String,String)]
utpBaseAliases
  = [ alCondL1, alCondL2, alCondL3, alCondL4
    , alCondL5a, alCondL5b, alCondL6, alCondL7
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
            , known   =  newVarTable
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
nat  = GivenType $ fromJust $ ident "N"
int  = GivenType $ fromJust $ ident "Z"
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
