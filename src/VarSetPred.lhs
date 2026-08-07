\chapter{Variable-Set Predicates}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2026

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module VarSetPred (
  VSetPred(..)
, isFalseVSP, falseVSPmsg
, vspGVar, vspVSet, vspAllVars, vspCoverage, vspInvolved
, vsEmpty, vsSngl, vsList, vsUnion, vsMinus
, vsDisj, vsSub, vsSubD
) where
import Data.Char(isSpace)
import Data.Set(Set)
import qualified Data.Set as S
import LexBase
import Variables

import Debugger
\end{code}

\section{Introduction}

We provide set-expressions and predicates built over \h{VarSet},
along with constructors and simplifiers.
We assume our basic building blocks to be enumerations of general variables:
$$\setof{gv_1,\dots,gv_n}, \qquad n \geq 0 .$$
These can then be combined with set-theoretic operators 
($\cup$,$\cap$,$\setminus$) 
to produce set expressions.
We then add set-theoretic relations 
($=$,$\subseteq$,$\disj$) 
over such expressions, to produce set predicates.

\section{Variable-Set Predicates}

We want predicates that relate two set-expressions.
The relations that we want are 
disjointness ($\disj$),
subset ($\subseteq$),
and a version of subset restricted to dynamic variables ($\subseteq_d$).
Dynamic subset ($\subseteq_d$) is defined as:
$$
  g \subseteq_d X \quad \defs \quad (g|d) \subseteq (X|d)
$$
where $S|d$ is $S$ restricted to the dynamic variables in scope.
The key question is: does this affect the laws?
The answer is no, because being dynamic is a pointwise property
and restriction w.r.t a set element distributes through the set operators.
\begin{eqnarray*}
   \emptyset|d &\defs& \emptyset
\\ \setof{x}|d &\defs& \setof{x} \cond{x \textit{ is dynamic}} \emptyset
\\ (S\cup T)|d &\defs& (S|d) \cup (T|d)
\\ (S\cap T)|d &\defs& (S|d) \cap (T|d)
\\ (S\setminus T)|d &\defs& (S|d) \setminus (T|d)
\end{eqnarray*}


\begin{code}
data VSetPred
  =  VSFalseP String -- yes, we need this
  |  VSDisj  GenVar VarSet  
  |  VSSub   GenVar VarSet 
  |  VSSubD  GenVar VarSet  -- limited to dynamic vars
  |  VSTrueP
  deriving (Eq,Ord,Show,Read)
\end{code}

\subsection{Variable-Set Predicate Queries}

Falsehood check:
\begin{code}
isFalseVSP :: VSetPred -> Bool
isFalseVSP (VSFalseP _)  =  True
isFalseVSP _             =  False

falseVSPmsg :: VSetPred -> String
falseVSPmsg (VSFalseP msg)  =  msg
falseVSPmsg _               =  ""
\end{code}

Extracting sub-components:
\begin{code}
vspGVar :: MonadFail mf => VSetPred -> mf GenVar
vspGVar (VSDisj gv _)  =  return gv
vspGVar (VSSub  gv _)  =  return gv
vspGVar (VSSubD gv _)  =  return gv
vspGVar _              =  fail "VSetPred has no GenVar"

vspVSet :: VSetPred -> VarSet
vspVSet (VSDisj gv vset)  =  vset
vspVSet (VSSub  gv vset)  =  vset
vspVSet (VSSubD gv vset)  =  vset
vspVSet _                 =  S.empty
\end{code}

All mentioned variables:
\begin{code}
vspAllVars :: VSetPred -> VarSet
vspAllVars (VSDisj gv vset)  =  S.insert gv vset
vspAllVars (VSSub  gv vset)  =  S.insert gv vset
vspAllVars (VSSubD gv vset)  =  S.insert gv vset
vspAllVars _                 =  S.empty
\end{code}

General variables covered by variable-set predicate:
\begin{code}
vspCoverage :: VSetPred -> VarSet
vspCoverage (VSSub  gv vset)  =  vset
vspCoverage (VSSubD gv vset)  =  vset
vspCoverage _                 =  S.empty

vspInvolved :: VSetPred -> VSetPred -> VarSet
vsp1 `vspInvolved` vsp2  =  vspAllVars vsp1 `vsIntsct` vspAllVars vsp2
\end{code}

\subsection{Variable-Set Builders}

We use \h{VarSet}, and give constructor style names to set operations:
\begin{code}
vsEmpty :: VarSet
vsEmpty = S.empty

vsSngl :: GenVar -> VarSet
vsSngl = S.singleton

vsList :: VarList -> VarSet
vsList = S.fromList

vsUnion :: VarSet -> VarSet -> VarSet
vsUnion = S.union

vsIntsct :: VarSet -> VarSet -> VarSet
vsIntsct  = S.intersection

vsMinus :: VarSet -> VarSet -> VarSet
vsMinus = S.difference
\end{code}


\subsection{Simplifying Variable-Set Predicates}

While we define sensible VS-predicates when defining assertions,
these are also produced when matches are instantiated.
It helps to have a way to check such predicates to see if they can be
simplified to true, false, or some reduced form.
We define smart builders that perform these checks.

We assume general variable $V$ 
that can be instantiated as one of $x$, $T$, or $\lst x$.
We also use $W$ to represent other general variables.

We use the notation $cond ~\vdash~ pred ~\mapsto~ pred'$ 
to assert that if $cond$ is true, then $V~rel~S$ can be reduced to $pred'$.
The $cond$ in the next row is the negation of the $pred$ in the row above.
The left column accumulates what needs to be false to get any given row.
The blank $cond$ in the first row always implicitly $\true$.

\def\is{\mathrel{\text{is}}}

\subsubsection{Smart Disjoint}

$$ V \disj D $$
$$
\begin{array}{l@{~\vdash~}l@{~\mapsto~}l}
   & D=\emptyset 
   & \true
%
\\ D \neq \emptyset 
   & V \mof D 
   & \false
%
\\ V \notin D 
   & V \is x \land \forall W \mof D \have obs(W) 
   & \true
\end{array}
$$
\begin{code}
vsDisj :: GenVar -> VarSet -> VSetPred
vsDisj gv vs
  | S.null vs                       =  VSTrueP
  | gv `S.member` vs                =  VSFalseP "vsDisj: gv in vs"
  | isObsGVar gv 
    && all isObsGVar (S.toList vs)  =  VSTrueP
vsDisj gv vs                        =  VSDisj gv vs
\end{code}

\newpage
\subsubsection{Smart Subset}

$$ V \subseteq C $$
$$
\begin{array}{l@{~\vdash~}l@{~\mapsto~}l}
   & V \mof C 
   & \true
%
\\ V \notin C 
   & obs(V) \land C = \emptyset 
   & \false
\\ & obs(V) \land \forall W \mof C \have obs(W) 
   & \false
\end{array}
$$
\begin{code}
vsSub :: GenVar -> VarSet -> VSetPred
vsSub gv vs
  | gv `S.member` vs  =  VSTrueP
  | isObsGVar gv
    && S.null vs      =  VSFalseP "vsSub: obs-var not in null vs"
  | isObsGVar gv 
    && all isObsGVar (S.toList vs)  
                      =  VSFalseP "vsSub: obs-var not in obs-varset"
vsSub gv vs =  VSSub gv vs
\end{code}

\subsubsection{Smart Dynamic Subset}


$$ V \subseteq_a C_a $$
$$
\begin{array}{l@{~\vdash~}l@{~\mapsto~}l}
   & \lnot dyn(V) 
   & \false
%
\\ dyn(V) 
   & V \mof (C_a|d)
   & \true
%
\\ V \notin (C_a|d)
   & obs(V) \land (C_a|d) = \emptyset 
   & \false
\\ & obs(V) \land \forall W \mof (C_a|d) \have obs(W) 
   & \false
\end{array}
$$
Note: if $C_a$ is defined properly, then $C_a|d$ does not change anything.
\begin{code}
vsSubD :: GenVar -> VarSet -> VSetPred
vsSubD gv _ | not (isDynGVar gv)  =  VSFalseP "vsSubD: gv not dynamic"
vsSubD gv vs 
  = case vsSub gv (S.filter isDynGVar vs) of
      VSSub gv' vs'  ->  VSSubD gv' vs'
      vsp            ->  vsp
\end{code}



\subsection*{Not Used, Currently Deprecated}

In addition, 
we have an interpretation of predicate $S_1 ~rel~S_2$
where $S_1$ represents a set $G$ (usually singleton)
that is an enumeration of variables that denote term free-variables,
while $S_2$ is a general variable set $V$.

\textbf{Note: }
We need to check for each $rel$ that the following holds:
$$(G_1\cup G_2)~rel~V 
  \quad = \quad
  (G_1\cup~rel~V) \land (G_2~rel~V)
$$
\begin{eqnarray*}
   (G_1\cup G_2)~\disj~V 
   \quad = \quad
  (G_1~\disj~V) \land (G_2~\disj~V)
\\ (G_1\cup G_2)~\subseteq~V 
  \quad = \quad
  (G_1~\subseteq~V) \land (G_2~\subseteq~V)
\end{eqnarray*}
Exercise: prove the above.

An issue that arises is how to simplify two such predicates,
where $G_1 = G_2 = G$.
$$ (G~rel_1~V_1) \land (G~rel_2~V_2) \quad = ?$$
This breaks down into two sub-categories:
same predicate ($rel_1=rel_2$),
and different predicate ($rel_1 \neq rel_2$).

\subsubsection{Same Predicate Simplification}

We start with some same-predicate simplification laws,
that reduce a list of predicates with the same relation down to 
a single instance of that relation.
\begin{code}
enumSamePred :: VSetPred -> VSetPred -> VSetPred
enumSamePred (VSDisj gv1 vs1) (VSDisj gv2 vs2)
  | gv1 == gv2  = enumSameDisj gv1 vs1 vs2
enumSamePred (VSSub gv1 vs1) (VSSub gv2 vs2)
  | gv1 == gv2  = enumSameSub gv1 vs1 vs2
enumSamePred (VSSubD gv1 vs1) (VSSubD gv2 vs2)
  | gv1 == gv2  = enumSameSubD gv1 vs1 vs2
enumSamePred f@(VSFalseP _) _ = f
enumSamePred _ f@(VSFalseP _) = f
enumSamePred vsp1 VSTrueP = vsp1
enumSamePred vsp1 vsp2 = VSFalseP "enumSamePred: differing relations."
\end{code}
\begin{eqnarray*}
   G \disj D_1 \land G \disj D_2
   &=& G \disj (D_1 \cup D_2)
\\ G \subseteq C_1 \land G \subseteq C_2
   &=& G \subseteq (C_1 \cap C_2)
\\ G \subseteq_d Cd_1 \land G \subseteq_d Cd_2 
   &=& G \subseteq_d (Cd_1 \cap Cd_2)
\end{eqnarray*}
\begin{code}
enumSameDisj :: GenVar -> VarSet -> VarSet -> VSetPred
enumSameDisj gs vs1 vs2 = VSDisj gs (vs1 `vsUnion` vs2)
enumSameSub :: GenVar -> VarSet -> VarSet -> VSetPred
enumSameSub gs vs1 vs2 = VSSub gs (vs1 `vsIntsct` vs2)
enumSameSubD :: GenVar -> VarSet -> VarSet -> VSetPred
enumSameSubD gs vs1 vs2 = VSSubD gs (vs1 `vsIntsct` vs2)
\end{code}


\subsubsection{Different Predicate Simplification}

We continue with the following four different-predicate normalising laws,
that combine and simplify relations as much as possible.
\begin{eqnarray*}
   G \disj D \land G \subseteq C 
   &=& G \disj (D \setminus C) \land G \subseteq (C \setminus D)
\\ G \disj D \land G \subseteq_d Cd 
   &=& G \disj (D \setminus Cd) \land G \subseteq_d (Cd \setminus D)
\\ G \subseteq C \land G \subseteq_d Cd 
   &=& G \subseteq_d (C \cap Cd)
\\ G \disj D \land G \subseteq C \land G \subseteq_d Cd 
   &=& G \disj (D \setminus Cd) \land g \subseteq_d (Cd \setminus D)
\end{eqnarray*}


