\section{XYZ Theory}
\begin{verbatim}
Copyright  Andrew Buttefield, Danny Thomas (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module XYZ (
 xyzConjs, xyzName, xyzTheory
) where

import Data.Maybe
import qualified Data.Set as S

import Symbols

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
nat  = GivenType $ fromJust $ ident "N"
int  = GivenType $ fromJust $ ident "Z"
\end{code}

$$ e \quad \lst e  \qquad f \quad \lst f$$
\begin{code}
-- Underlying variables:
ve = Vbl (fromJust $ ident "e") ExprV Before
vf = Vbl (fromJust $ ident "f") ExprV Before
vg = Vbl (fromJust $ ident "g") ExprV Before
-- for use in expressions
e = fromJust $ eVar ArbType ve
f = fromJust $ eVar ArbType vf
g = fromJust $ eVar ArbType vg
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
psub var expr pred = Sub P pred $ fromJust $substn [(var,expr)] []
esub var expr1 expr2 = Sub (E ArbType) expr2 $ fromJust $substn [(var,expr1)] []
sub_x_by_e p = psub vx e p
sub_xs_by_es p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
lvxs = LVbl vx [] []
qxs = LstVar lvxs
\end{code}

\newpage
\subsection{XYZ alphabet}

The alphabet for this theory is $\setof{x,y,z,x',y',z'}$.

% We also have a known predicate variable $\Skip$,
% defined to be $x'=x \land y'=y \land z'=z$.

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

\subsubsection{Skip}
$$
  \begin{array}{lll}
     \II
     \defs
       x'=x \land y'=y \land z'=z
     &
     & \QNAME{XYZ-$\II$-Def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
--v_skip = Vbl (jId "II") PredV Static
skipDef = x' `isEqualTo` x /\ ( y' `isEqualTo` y /\ z' `isEqualTo` z)

axXYZSkipDef = preddef ("XYZ" -.- "skip" -.- "def")
                       ( skip === skipDef)
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
mkAsg (Var _ x) e = Sub P theAssignment $ jSubstn [(x,e)] []

mkCond p b q = PCons True (fromJust $ ident "cond")[p, b, q]


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

\subsubsection{Conditional}
$$
  \begin{array}{lll}
     \ifte c P Q
     \defs
       c \land P \lor \lnot c \land Q
     &
     & \QNAME{XYZ-$\lhd\rhd$-Def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axXYZCondDef = preddef ("XYZ" -.- "<|>" -.- "def")
                       ( cond p c q === (c /\ p) \/ ((mkNot c) /\ q))
                       scTrue
\end{code}

\newpage
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
before r = Sub P r $ fromJust $ substn [(vx',xm),(vy',ym),(vz',zm)] []
after r  = Sub P r $ fromJust $ substn [(vx,xm), (vy,ym), (vz,zm)] []

axXYZSeqDef = preddef ("XYZ" -.- ";" -.- "def")
                   ( mkSeq p q
                     ===
                     exists [qxm,qym,qzm]
                      (before p /\ after q)  )
                    scTrue
\end{code}

\subsubsection{While}
This is not the formal definition for now - just the loop-unrolling law.
$$
  \begin{array}{lll}
     \whl c P
     \defs
       (P;c \circledast P) \lhd c \rhd skip
     &
     & \QNAME{XYZ-$\circledast$-Def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axXYZWhileDef = preddef ("XYZ" -.- "while" -.- "def")
                       ( while c p  
                         === 
                         cond (mkSeq p (while c p)) c skip)
                       scTrue
\end{code}




We now collect our axiom set:
\begin{code}
xyzAxioms :: [Law]
xyzAxioms
  = map labelAsAxiom
      [ axXYZSkipDef
      , axXAsgDef
      , axYAsgDef
      , axZAsgDef
      , axXYZCondDef
      , axXYZSeqDef
      , axXYZWhileDef
      ]
\end{code}

\subsection{XYZ Conjectures}

\subsubsection{Skip}
$$
\begin{array}{rcll}
   \II         &=&  x:=x, \quad x \in A & \SkipAltN
\end{array}
$$\par\vspace{-8pt}
\begin{code}
cjSkipAlt = preddef ("II" -.- "alt")
                    (skip === mkAsg x x)
                    scTrue
\end{code}

\newpage
\subsubsection{Sequential Composition}
$$
\begin{array}{rcll}
   \II;P         &=&  P  & \SeqLUnitN
\\ P;\II         &=&  P  & \SeqRUnitN
\\ P;(Q;R) &=& (P;Q);R & \SeqAssocN
\\ (P \lor Q);R   &=& (P;Q) \lor (Q;R) &  \OrSeqDistrN
\\ P;(Q \lor R)   &=& (P;Q) \lor (P;R) &  \SeqOrDistrN
\\ P;(Q \land b') &=& (P;Q) \land b'   &  \PreSeqN
\\ (b \land P);Q  &=& b \land (P;Q)     &  \PostSeqN
\end{array}
$$


\begin{code}
cjSeqAssoc = preddef ("seq" -.- "assoc")
                   ( mkSeq (mkSeq p q) r === mkSeq p (mkSeq q r))
                   scTrue
cjOrSeqDistr = preddef ("lor" -.- "seq" -.- "distr")
                    (mkSeq (p \/ q) r === (mkSeq p r) \/ (mkSeq q r))
                    scTrue
cjSeqOrDistr = preddef ("seq" -.- "lor" -.- "distr")
                    (mkSeq p (q \/ r) === (mkSeq p q) \/ (mkSeq p r))
                    scTrue
\end{code}

\subsubsection{Conditional}
$$
\begin{array}{rcll}
   \ifte \true P Q &=& Q & \CondTrueN
\\ \ifte \false P Q &=& Q & \CondFalseN
\\ (\ifte c P Q);R &=& \ifte c {(P;R)} {(Q;R)} & \CondSeqDistrN
\\ \ifte c P {(Q \lor R)} &=& (\ifte c P Q) \lor (\ifte c P R) & \CondOrDistrN
\\ P \lor (\ifte c Q R) &=& \ifte c {(P \lor Q)} {(P \lor R)} & \OrCondDistrN
\end{array}
$$
\begin{code}
vjConjTrue = preddef ("cond" -.- "true")
                     (mkCond p trueP q === p)
                     scTrue
vjConjFalse = preddef ("cond" -.- "false")
                     (mkCond p falseP q === p)
                     scTrue
cjCondSeqDistr = preddef ("cond" -.- "seq" -.- "distr")
                  ( mkSeq (mkCond p b q) r === mkCond (mkSeq p r) b (mkSeq q r))
                   scTrue
cjCondOrDistr = preddef ("cond" -.- "lor" -.- "distr")
                    (mkCond p b (q \/ r) === (mkCond p b q) \/ (mkCond p b r))
                    scTrue
cjOrCondDistr = preddef ("lor" -.- "cond" -.- "ldistr")
                    (p \/ mkCond q b r === mkCond (p \/ q) b (p \/ r))
                    scTrue
\end{code}

\newpage
\subsubsection{Substitution}
$$
\begin{array}{rcll}
   P[x/y][y/x] &=& P, \quad x \notin P &  \SubInvN
\\ P[e/x][f/x] &=& P[e[f/x]/x] & \SubCompN
\\ P[e/x][f/y] &=& P[f/y][e/x] \quad y\notin e,x\notin f & \SubSwapN
\end{array}
$$
These are not provable right now. We add them as pseudo-axioms for now.
\begin{code}
hypSubInv = preddef 
           ("sub" -.- "inv")
           ( psub vx y (psub vy x p)
             ===
             p )
           ([StdVar vx] `notin` StdVar vp)
hypSubComp = preddef 
           ("sub" -.- "comp")
           ( psub vx e (psub vx f p)
             ===
             psub vx (esub vx f e) p )
           scTrue
hypSubSwap = preddef 
           ("sub" -.- "swap")
           ( psub vx e (psub vy f p)
             ===
             psub vx e (psub vy f p) )
           ( fromJust ( mrgSideCond []
                          ([StdVar vx] `notin` StdVar vf)
                          ([StdVar vy] `notin` StdVar ve) ) )
\end{code}


 
\newpage
\subsubsection{Assignment}
$$
\begin{array}{rcll}
   x:=e;x:=f &=& x:=f[e/x] & \AsgSeqN
\\ x:=e;y:=f &=& y:=f[e/x]; x:=e & \AsgSwapN
\end{array}
$$\par\vspace{-8pt}
\begin{code}
cjAsgSeq = preddef ("asg" -.- "seq")
                   ( mkSeq (mkAsg x e) (mkAsg x f)
                     ===
                    (mkAsg x (Sub (E ArbType) f 
                                $ fromJust $ substn [(vx,e)] [])) )
                   scTrue
cjAsgSwap = preddef ("asg" -.- "swap")
                    ( mkSeq (mkAsg x e) (mkAsg y f) 
                      ===
                      mkSeq 
                        (mkAsg y (Sub (E ArbType) f 
                                    $ fromJust $ substn [(vx,e)] [])) 
                        (mkAsg x e) )
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
  = [ cjSkipAlt
    , cjSeqAssoc, cjOrSeqDistr, cjSeqOrDistr
    , vjConjTrue, vjConjFalse
    , cjCondSeqDistr
    , cjCondOrDistr
    , cjOrCondDistr
    , cjAsgSeq, cjAsgSwap
    ]
\end{code}
and our temporary law set:
\begin{code}
xyzHyps :: [Law]
xyzHyps
  = map labelAsAxiom
        [ hypSubInv
        , hypSubComp
        , hypSubSwap
        ]
\end{code}

\subsection{The Predicate Theory}

\begin{code}
xyzName :: String
xyzName = "XYZ"
xyzTheory :: Theory
xyzTheory
  =  nullTheory { thName  =  xyzName
            , thDeps  =  [ --utpBaseName
                           uCloseName
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
            , known   =  xyzKnown
            , laws    =  xyzAxioms ++ xyzHyps
            , conjs   =  xyzConjs
            }
\end{code}
