\section{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  pattern Unif, pattern NonU
, AtmSideCond
, pattern Disjoint, pattern CoveredBy
, ascGVar, ascVSet
, SideCond, scTrue, isTrivialSC
, onlyFreshSC, onlyInvolving, onlyFreshOrInvolved
, scGVars, scVarSet
, mrgAtmCond, mrgSideCond, mrgSideConds, mkSideCond
, scDischarge
, isFloatingASC
, notin, covers, fresh
, citingASCs
, int_tst_SideCond
) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import LexBase
import Variables
import AST
import VarData

import Test.HUnit hiding (Assertion)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}


\newpage
\subsection{Introduction}

A side-condition is a property used in laws,
typically putting a constraint on the free variables of some term.
In many logics, these can be checked by simple inspection of a term.
However,
given a logic like ours with explicit expression and predicate
(a.k.a. \emph{schematic}) variables this is not always possible.

A side condition is about a relationship between the free variables
of term ($T$),
and a set of other (general) variables ($x,\lst{v}$).
In general with have a conjunction of atomic conditions,
but we need to be able to distinguish between no conditions (always ``true'')
and inconsistent conditions
(e.g. $x \disj \fv(T) \land x = \fv(T) $, always ``false'').
As a false side-condition means a match failure,
we do not represent them explicitly.
Instead, any operation on side-conditions that could result
in an inconsistent result should fail, gracefully.

\subsubsection{Atomic Side-Conditions}

An atomic side-condition (ASC) can have one of the following forms,
where $T$ abbreviates $\fv(T)$:
\begin{eqnarray*}
   x,\lst v   \disj  T
   && \mbox{disjoint, short for }\{x,\lst v\} \cap \fv(T) = \emptyset
\\ x,\lst v \supseteq T && \mbox{covering}
\\ pre      \supseteq T && \mbox{pre-condition, no dashed variables}
\end{eqnarray*}
In most cases the term $T$ will be very general,
and will be represented by a variable.
In some cases, we will use a list-variable to denote a list of terms,
usually expressions, and we will expect there to be only one general variable
which will itself be a list variable:
\begin{eqnarray*}
   \lst v   \disj  \lst e && \mbox{disjoint, short for }
   v_1\disj \fv(e_1) \land \dots \land v_n\disj \fv(e_n)
\end{eqnarray*}
This arises when we have side-conditions between lists of variables
and expressions that occur in substitutions.

We note that disjointness and being a (pre-)condition
distribute through conjunction without restrictions,
so we have, for example, that:
\begin{eqnarray*}
   x,y \disj S,T
   &\equiv&
   x \disj S \land x \disj T \land y \disj S \land y \disj T
\\ pre \supseteq S,T
   &\equiv&
   pre \supseteq S \land pre \supseteq T
\end{eqnarray*}
However, covering only distributes (like $pre$) w.r.t. conjunction
as far as terms are concerned.
The variable-list must be retained as a unit.
\begin{eqnarray*}
   x \supseteq S,T
   &\equiv&
   x \supseteq S \land x \supseteq T
\\ x,y \supseteq T
   &\not\equiv&
   x \supseteq T \land y \supseteq T
\end{eqnarray*}
In general we are assuming that law side-conditions have term variables,
but when we instantiate such side-conditions with a match binding,
we may find observational variables appearing.
In some of these cases, we may be able to simplify a side-condition further:
\begin{eqnarray*}
   \dots,z,\dots   \disj  z  && \false
\\ \dots,z,\dots{} \supseteq z  && \true
\\ \emptyset \supseteq z && \false
\\ pre      \supseteq z  && z \textrm{ is a \texttt{Before} variable}
\end{eqnarray*}

We also need to take account of known variables of various kinds
when evaluating and building side-conditions.

\newpage
\subsubsection{Side-Condition Temporality}

Finally, we need to consider the use of dynamic normalisation here,
in which $x' \supseteq t'$ (say)
actually means
$
 x \supseteq t \land x' \supseteq t' \land x_n \supseteq t_n
$, for all subscripts $n$.
This only makes sense if the side-condition is ``temporally uniform'',
in that all variables involved have the same temporality.

In UTP,
we typically use uppercase letters ($P, Q, \dots$) to denote predicates that
denote pre/post relations.
The predicates they represent are usually a mix of before- and after-variables.
When a predicate is a pre-condition (only using before-variables),
we usually denote this using lowercase letters ($p, q, \dots$).
For a post-condition, only using after-variables,
we denote this using dashed lower-case letters ($p', q', \dots$).

Any side-condition with a relational predicate variable
(e.g. $x \disj P$)
is not temporally uniform.
A side-condition with before-variables and a pre-condition
(e.g. $x \disj q$)
is temporally uniform.
The same holds when after-variables and post-conditions are used
(e.g. $x' \supseteq q'$).
A non-uniform disjointness condition
(e.g. $x \disj p'$)
is vacuously true.
A non-uniform superset condition
(e.g. $y' \supseteq q$)
is vacuously false.

A predicate variable $P$ is represented as a \texttt{Static PVar},
while $p$ and $p'$ are represented as \texttt{Before} and \texttt{After}
\texttt{PVar}s respectively.
A similar convention is used for expression and observation variables.

A temporally uniform condition is represented using \texttt{Before}
variables throughout,
and is interpreted as covering cases where \texttt{Before}
is uniformly replaced by \texttt{After}, or \texttt{During n},
for that same value of \texttt{n}.
For example,
$x' \disj p'$ is represented as $x \disj p$,
and is also interpreted as $x_i \disj p_i$ for any $i$.

Since $P$, or $p$ or $p'$ are shorthand for $fv(P)$ etc.,
they denote sets of variables here.
Since list-variables denote variable sets/lists, the same relationships hold,
and the uniformity property carries over.

We will have a flag to indicate uniformity,
that will be set when a side-condition is specified/built.
We do this as almost all side-condition usage
will need to check for this property.
\begin{code}
data Uniformity
  = UN -- Uniform
  | NU -- Not Uniform
  deriving (Eq,Ord,Show,Read)
pattern Unif = UN
pattern NonU = NU
\end{code}

\subsection{Atomic Side-Conditions}

We now introduce our notion of an atomic-side condition.
We will not represent $pre$ explicitly here,
and instead will use $\lst O \supseteq T$ (which is non-uniform!).
\begin{code}
data AtmSideCond
 = SD Uniformity GenVar VarSet -- Disjoint
 | SS Uniformity GenVar VarSet -- Superset (covers), and Pre
 deriving (Eq,Ord,Show,Read)
\end{code}
In the \texttt{SD} case, having an empty set reduces to \true,
while in the \texttt{SS} case,
an empty set asserts that the term denoted by the general variable is closed.
\begin{code}
pattern Disjoint  u gv vs = SD u gv vs  --  gv `intersect` vs = {}
pattern CoveredBy u gv vs = SS u gv vs  --  gv  `subsetof` vs
\end{code}
Sometimes we want the \texttt{GenVar} component,
\begin{code}
ascGVar :: AtmSideCond -> GenVar
ascGVar (Disjoint  _ gv _)     =  gv
ascGVar (CoveredBy _ gv _)  =  gv
\end{code}
or the \texttt{VarSet} part:
\begin{code}
ascVSet :: AtmSideCond -> VarSet
ascVSet (Disjoint  _ _ vs)     =  vs
ascVSet (CoveredBy _ _ vs)  =  vs
\end{code}

\subsubsection{Checking Atomic Sideconditions}

We need to ensure that the \texttt{Uniformity} component
of an atomic side-condition is set correctly.
\begin{code}
setASCUniformity :: AtmSideCond -> AtmSideCond
setASCUniformity (Disjoint  _ gv vs)
  | isUniform gv vs  =  Disjoint Unif (dnGVar gv) (S.map dnGVar vs)
  | otherwise        =  Disjoint NonU         gv                vs
setASCUniformity (CoveredBy _ gv vs)
  | isUniform gv vs  =  CoveredBy Unif (dnGVar gv) (S.map dnGVar vs)
  | otherwise        =  CoveredBy NonU         gv                vs

isUniform :: GenVar -> VarSet -> Bool
isUniform gv vs
  = S.size whens == 1 && isDynamic (head $ S.elems whens)
  where
    whens = S.map gvarWhen (S.insert gv vs)
\end{code}


It is also possible to simplify some proposed atomic side-conditions
to either true or false.
Here we provide a monadic function that fails if the condition
is demonstrably false,
and otherwise returns a \texttt{Maybe} type,
where \texttt{Nothing} denotes a condition that is true.
We need to do this in general
in the context of what is ``known'' about variables.
\begin{code}
mscTrue = Nothing
ascCheck :: MonadFail m => [VarTable] -> AtmSideCond -> m (Maybe AtmSideCond)
\end{code}
Here, $z$ denotes an (standard) observation variable,
$T$ denotes a standard term variable,
and $g$ denotes either $z$ or $T$.
We also use the case conventions described earlier ($P, p, p'$).

\paragraph{Checking Disjoint}

\begin{eqnarray*}
   \emptyset             \disj g           &&   \true
\\ \dots,z,\dots         \disj z           &&   \false
\\ \{stdObs\}\setminus z \disj z           &&   \true
\\ x                     \disj p'          &&   \true
\\ x'                    \disj p           &&   \true
\\ x                     \disj \lst \ell'  &&   \true
\\ x'                    \disj \lst \ell   &&   \true
\end{eqnarray*}
Note that we cannot deduce (here) that $T \disj T$ is false,
because $T$ could correspond to the empty set.
Nor can we assume $T \disj z$ is false, because $T$ could contain $z$.
\begin{code}
ascCheck vts asc@(Disjoint NU  sv@(StdVar v) vs)
  | S.null vs         =  return mscTrue
  | not $ isObsVar v  =  return $ Just $ setASCUniformity asc
  | sv `S.member` vs  =  report "atomic Disjoint is False"
  | all isStdV    vs  =  return mscTrue
  where
    showsv = "v = "++show v
    showvs = "vs = "++show vs
    report msg = fail $ unlines' [msg,showsv,showvs]
\end{code}

\paragraph{Checking CoveredBy}

\begin{eqnarray*}
   \emptyset             \supseteq z           && \false
\\ \dots,g,\dots{}       \supseteq g           && \true
\\ \{stdObs\}\setminus z \supseteq z           && \false
\\ x                     \supseteq p'          && \false
\\ x'                    \supseteq p           && \false
\\ x                     \supseteq \lst \ell'  && \false
\\ x'                    \supseteq \lst \ell   && \false
\end{eqnarray*}
Here, as $T$ could be empty,
we cannot deduce that $\emptyset \supseteq T$ is false.
Similarly, $T \supseteq z$ could also be true.
\begin{code}
ascCheck vts asc@(CoveredBy NU  sv@(StdVar v) vs)
  | sv `S.member` vs  =  return mscTrue
  | not $ isObsVar v  =  return $ Just $ setASCUniformity asc
  | S.null vs         =  report "atomic covers is False (null)"
  | all isStdV vs     =  report "atomic covers is False (all std)"
  where
    showsv = "v = "++show v
    showvs = "vs = "++show vs
    report msg = fail $ unlines' [msg,showsv,showvs]
\end{code}

For anything else, we just return the condition unchanged.
In particular, we cannot do anything with freshness at this point.
\begin{code}
ascCheck _ asc = return $ Just asc
\end{code}



\newpage
\subsection{Full Side Conditions}

Freshness is a special case of disjoint:
\begin{itemize}
  \item It applies to the whole goal or law
  \item If the pattern fresh variables are bound in a match,
       then the corresponding candidate variable
        must satisfy the Disjoint NU  side-condition against
       the entire goal.
  \item If the pattern fresh variables are floating (not bound in a match)
   then we can generate new candidate variables that
   do satisfy the Disjoint NU  side-condition against
  the entire goal.
\end{itemize}
We have to treat freshness as a top-level side-condition,
with no attachment to any specific term-variable.

A ``full'' side-condition is basically a list of ASCs,
interpreted as their conjunction,
along with a set defining fresh variables.
\begin{code}
type SideCond = ( [AtmSideCond]  -- all must be true
                , VarSet )       -- must be fresh
\end{code}

If the atomic condition list is empty,
then we have the trivial side-condition, which is always true:
\begin{code}
scTrue :: SideCond
scTrue = ([],S.empty)

isTrivialSC :: SideCond -> Bool
isTrivialSC ([],fvs)  =  S.null fvs
isTrivialSC _         =  False
\end{code}

We are also interested when the only side-conditions we
have are to do with freshness:
\begin{code}
onlyFreshSC :: SideCond -> Bool
onlyFreshSC (ascs,_) = null ascs
\end{code}
or involve variables in a designated set:
\begin{code}
onlyInvolving :: VarSet -> SideCond -> Bool
onlyInvolving involved (ascs,_) = all (onlyWith involved) ascs

onlyWith :: VarSet -> AtmSideCond -> Bool
onlyWith involved (SD _ gv vs) = gv `S.member` involved || involved `overlaps` vs
onlyWith involved (SS _ gv vs) = gv `S.member` involved || involved `overlaps` vs
\end{code}
We may accept either of the above:
\begin{code}
onlyFreshOrInvolved :: VarSet -> SideCond -> Bool
onlyFreshOrInvolved involved ([],_)    =  True
onlyFreshOrInvolved involved (ascs,_)  =  all (onlyWith involved) ascs
\end{code}

Finally,
sometimes we want all the general variables or variable-sets
from a side-condition:
\begin{code}
scGVars :: SideCond -> Set GenVar
scGVars (ascs,_) = S.fromList $ map ascGVar ascs

scVarSet :: SideCond -> VarSet
scVarSet (ascs,fvs) = (S.unions $ map ascVSet ascs) `S.union` fvs
\end{code}

\subsection{Merging Side-Conditions}

The list of ASCs
is kept ordered by the \texttt{GenVar} component,
If there is more than one ASC with the same general variable,
then they are ordered as follows:
\texttt{Disjoint},
then
\texttt{CoveredBy}.
We can only have at most one of each.

The function \texttt{mrgAtmCond} below is the ``approved'' way
to generate side-conditions,
by merging them in, one at a time,
into a pre-existing list ordered and structured as described above.

\begin{code}
mrgAtmCond :: MonadFail m => [VarTable]
           -> AtmSideCond -> [AtmSideCond] -> m [AtmSideCond]
\end{code}

1st ASC is easy:
\begin{code}
mrgAtmCond vts asc []
  = do masc <- ascCheck vts asc
       case masc of
         Nothing ->  return [] -- asc is in fact true
         Just asc' -> return [asc']
\end{code}

Subsequent ones mean searching to see if there are already ASCs with the
same general-variable:
\begin{code}
mrgAtmCond vts asc ascs
  = do masc <- ascCheck vts asc
       case masc of
         Nothing ->  return ascs
         Just asc' -> splice (mrgAtmAtms vts asc) $ brkspnBy (compareGV asc) ascs

compareGV asc1 asc2  =  ascGVar asc1 `compare` ascGVar asc2
sameGV asc1 asc2     =  asc1 `compareGV` asc2 == EQ
\end{code}

\subsubsection{Merging one ASC with relevant others}

Now, merging an ASC in with other ASCs referring to the same general variable:
\begin{code}
mrgAtmAtms :: MonadFail m => [VarTable]
           -> AtmSideCond -> [AtmSideCond] -> m [AtmSideCond]
mrgAtmAtms vts asc [] = return [asc] -- it's the first.
\end{code}

Given one or more pre-existing ASCs for this g.v., we note the following possible
patterns:
\begin{verbatim}
[Disjoint]  [Disjoint,CoveredBy] [CoveredBy]
\end{verbatim}
If the general variable is required to be fresh,
then this is inconsistent with \texttt{CoveredBy}.

\subsubsection{ASC Merge Laws}

We have the following interactions,
where $D$ and $C$ are the variable-sets found
in \texttt{Disjoint} and \texttt{CoveredBy} respectively.
So the semantics of the Disjoint NU  ($D$) and covering ($C$) variable-sets,
parameterised by a general variable $G$,
are:
\begin{eqnarray*}
  \sem{\_}_{\_} &:& \power V \fun V \fun (V \fun \Bool)
\\ \sem{D}_G &=& \fv.G \cap D = \emptyset
\\ \sem{C}_G &=& \fv.G \subseteq C
\\         &=& \fv.G = \emptyset, \quad \IF \quad C = \emptyset
\end{eqnarray*}
We get the following laws:
\begin{eqnarray*}
   \sem{D_1}_G \land \sem{D_2}_G &=&  \sem{D_1 \cup D_2}_G
\\ \sem{C_1}_G \land \sem{C_2}_G &=&  \sem{C_1 \cap C_2}_G
\\ \sem{D}_G \land \sem{C}_G
   &=&  \sem{D}_G \land \sem{C \setminus D}_G
\\ &=& \sem{C \setminus D}_G, \quad \IF \quad C\setminus D \neq \emptyset
\\ &=& \fv.G = \emptyset, \quad \IF \quad C\setminus D = \emptyset
\end{eqnarray*}
We not that an apparent contradiction between $D$ and $C$ (when $D \supseteq C$)
becomes a assertion that $G$ is closed
for any given general variable $G$,
we will have that $D$ and $C$ are disjoint.

Below, we overload the notation to denote the corresponding condition.
So, for example, depending on context,
$D$ can denote a variable-set
or the predicate $D \disj G$ ($G$ being the general variable in question).


\newpage
\subsubsection{Merging \texttt{Disjoint} into ASC}
\begin{code}
mrgAtmAtms vts (Disjoint NU  gv d0) [Disjoint NU  _ d1,CoveredBy NU  _ c]
 | c `S.isSubsetOf` d'  =  return [CoveredBy NU  gv S.empty]
 | otherwise            =  return [Disjoint NU  gv d',CoveredBy NU  gv (c S.\\ d')]
 where d' = d0 `S.union` d1
mrgAtmAtms vts (Disjoint NU  gv d0) [Disjoint NU  _ d1]
                  =  return [Disjoint NU  gv (d0 `S.union` d1)]
mrgAtmAtms vts (Disjoint NU  gv d) [CoveredBy NU  _ c]
 | c `S.isSubsetOf` d  =  return [CoveredBy NU  gv S.empty]
 | otherwise           =  return [Disjoint NU  gv d,CoveredBy NU  gv (c S.\\ d)]
\end{code}


\subsubsection{Merging \texttt{CoveredBy} into ASC}
\begin{code}
mrgAtmAtms vts (CoveredBy NU  gv c0) [Disjoint NU  _ d,CoveredBy NU  _ c1]
 | c' `S.isSubsetOf` d  =  return [CoveredBy NU  gv S.empty]
 | otherwise            =  return [Disjoint NU  gv d,CoveredBy NU  gv (c' S.\\ d)]
 where c' = c0 `S.union` c1
mrgAtmAtms vts (CoveredBy NU  gv c) [Disjoint NU  _ d]
 | c `S.isSubsetOf` d  =  return [CoveredBy NU  gv S.empty]
 | otherwise           =  return [Disjoint NU  gv d,CoveredBy NU  gv (c S.\\ d)]
mrgAtmAtms vts (CoveredBy NU  gv c0) [CoveredBy NU  _ c1]
               =  return [CoveredBy NU  gv (c0 `S.intersection` c1)]
\end{code}

\subsubsection{Failure Case}
If none of the above arise, then we currently have a problem,
probably with \texttt{mrgAtmCond} above.
\begin{code}
mrgAtmAtms vts atm atms
 = fail $ unlines' [ "Unexpected fail in mrgAtmAtms:"
                   , "atm is "++show atm
                   , "atms are "++ show atms
                   , "vts is "++show vts]
\end{code}

\subsubsection{Merging Atomic Lists}

\begin{code}
mrgAtmCondLists :: MonadFail m => [VarTable]
                -> [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
mrgAtmCondLists vts ascs1 [] = return ascs1
mrgAtmCondLists vts ascs1 (asc:ascs2)
     = do ascs1' <- mrgAtmCond vts asc ascs1
          mrgAtmCondLists vts ascs1' ascs2
\end{code}

\subsubsection{Merging Atomic and Freshness Side-Conditions}


\begin{code}
mrgAtomicFreshConditions :: MonadFail m => [VarTable]
                         -> VarSet -> [AtmSideCond] -> m SideCond
mrgAtomicFreshConditions vts freshvs ascs
  | freshvs `disjoint` coverVarsOf vts ascs  =  return (ascs,freshvs)
  -- the above might not work - `disjoint` may need vts information
  | otherwise  =  fail "Fresh variables cannot cover terms."

coverVarsOf :: [VarTable] -> [AtmSideCond] -> VarSet
coverVarsOf vts ascs = S.unions $ map coversOf ascs
coversOf (CoveredBy NU  _ vs)  =  vs
coversOf _              =  S.empty
\end{code}

\subsection{From ASC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: MonadFail m => [VarTable] -> [AtmSideCond] -> VarSet -> m SideCond
mkSideCond vts ascs fvs
 = do ascs' <-  mrgAtmCondLists vts [] ascs
      mrgAtomicFreshConditions vts fvs ascs'
\end{code}


\subsubsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each ASC and fresh set from the one into the other,
one at a time.
\begin{code}
mrgSideCond :: MonadFail m => [VarTable] -> SideCond -> SideCond -> m SideCond
mrgSideCond vts (ascs1,fvs1) (ascs2,fvs2)
     = do ascs' <- mrgAtmCondLists vts ascs1 ascs2
          mrgAtomicFreshConditions vts (fvs1 `S.union` fvs2) ascs'
          -- the above may require a vts-savvy union?

mrgSideConds :: MonadFail m => [VarTable] -> [SideCond] -> m SideCond
mrgSideConds vts [] = return ([],S.empty)
mrgSideConds vts (sc:scs)
  = do  scs' <- mrgSideConds vts scs
        mrgSideCond vts sc scs'
\end{code}

\newpage
\subsection{Discharging Side-conditions}

Here we simply check validity of $sc'_G \implies sc'_L$,
where $sc'_G$ is the goal side-condition,
and $sc'_L$ is the law side-condition translated into goal ``space''
after a successful match.
Because we may be handing side-conditions with ``questionable'' variables,
we attempt to return a simplified side-condition
that has the questionable bits that are not dischargeable.
If we discover a contradiction,
then we need to signal this,
because \texttt{SideCond} cannot represent a false side-condition explicitly.
\begin{code}
scDischarge :: MonadFail m => [VarTable] -> SideCond -> SideCond -> m SideCond
\end{code}
We have something of the form:
$$
 \left( \bigwedge_{i \in 1 \dots m} G_i \land G_F \right)
 \vdash
 \left( \bigwedge_{j \in 1 \dots n} L_j \land L_F  \right)
$$
Here $G_F$ and $L_F$ are the fresh variables associated with
goal and law respectively.
As these are global,
the plan is first to use the $G_i$ to discharge the $L_i$,
and then finish by using $G_F$ to discharge $G_L$ and any remaining $L_i$.

In our representation both the $G_i$ and $L_j$
are ordered by general variable ($V$).
So we can work through both lists,
using all the $G_i$ for a given g.v.,
to attempt to discharge all the $L_j$ for that same g.v.
Once this is complete, we then make use of the freshness information
to discharge further.

Success is when all such $L_j$ groups have been shown to be $\true$.
Failure occurs if any $L_j$ group results in $\false$.


\begin{code}
scDischarge vts anteSC@(anteASC,anteFvs) cnsqSC@(cnsqASC,cnsqFvs)
  | isTrivialSC cnsqSC  =  return scTrue  -- G => true   is   true
  | isTrivialSC anteSC  =  return cnsqSC  -- true => L   is   L, not discharged
  | otherwise
     = do asc' <- scDischarge' vts (groupByGV anteASC) (groupByGV cnsqASC)
          freshDischarge vts anteFvs cnsqFvs asc'
\end{code}

We have a modified version of \texttt{Data.List.groupBy}
\begin{code}
groupByGV :: [AtmSideCond] -> [(GenVar,[AtmSideCond])]
groupByGV []          =  []
groupByGV (asc:ascs)  =  (gv,asc:ours) : groupByGV others
                      where
                        gv               =  ascGVar asc
                        gv `usedIn` asc  =  gv == ascGVar asc
                        (ours,others)    =  span (usedIn gv) ascs
\end{code}

\subsubsection{Atomic Condition  Discharge}

Now onto processing those groups:
\begin{code}
scDischarge'  :: MonadFail m => [VarTable]
              -> [(GenVar,[AtmSideCond])] -> [(GenVar,[AtmSideCond])]
              -> m [AtmSideCond]
scDischarge' _ _ []      =  return []                   -- discharged
scDischarge' _ [] grpsL  =  return $ concat $ map snd grpsL -- not discharged
scDischarge' vts (grpG@(gvG,ascsG):restG) grpsL@(grpL@(gvL,ascsL):restL)
  | gvG < gvL  =  scDischarge' vts restG grpsL -- grpG not needed
  | gvG > gvL  =  do -- nothing available to discharge grpL
                     rest' <- scDischarge' vts restG restL
                     return (ascsL++rest')
  | otherwise  =  do -- use grpG to discharge grpL
                     ascs' <- grpDischarge vts ascsG ascsL
                     rest' <- scDischarge' vts restG restL
                     return (ascs'++rest')
\end{code}

\newpage

\textbf{As above, we only consider \texttt{Disjoint} and \texttt{CoveredBy}
for now.}

The following code assumes that the \texttt{GenVar} component
is the same in all of the \texttt{AtmSideCond}.

Here again, we have the form
\begin{equation}
 \left( \bigwedge_{i \in \setof{D,C,pre}} G_i \right)
 \vdash
 \left( \bigwedge_{j \in \setof{D,C,pre}} L_j \right)
 \label{eqn:SideCond:disharge-form}
\end{equation}
If we get here, then neither side-condition was trivially true,
so none of the lists here are empty.

Given that
\begin{eqnarray*}
   A \land B \implies C &=& (A \implies C) \lor  (B \implies C)
\\ A \implies B \land C &=& (A \implies B) \land (A \implies C)
\end{eqnarray*}
we can ask: in which order should we proceed?

Both orderings give the same outcome if all we want to do
is to simplify an instance of (\ref{eqn:SideCond:disharge-form}).
However, we are assuming all the $G_i$ are true,
and want to know if that is enough to ensure that all the $L_j$
are also true.
There is an asymmetry here, which means that we should
use all the $G_i$ to try and discharge each $L_i$,
rather than the other way around.
\begin{code}
grpDischarge :: MonadFail m => [VarTable]
             -> [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
grpDischarge _ _ []  =  return []
grpDischarge vts ascsG (ascL:ascsL)
  = do ascL'  <- ascsDischarge vts ascsG ascL
       ascsL' <- grpDischarge vts ascsG ascsL
       return (ascL'++ascsL')
\end{code}

Here we are trying to show
\begin{equation*}
 \left( \bigwedge_{i \in \setof{D,C,pre}} G_i \right)
 \vdash
 L_j \quad \where \quad j \in \setof{D,C,pre}
\end{equation*}
\begin{code}
ascsDischarge :: MonadFail m => [VarTable]
              -> [AtmSideCond] -> AtmSideCond -> m [AtmSideCond]
ascsDischarge _ [] ascL = return [ascL]
ascsDischarge vts (ascG:ascsG) ascL
  =  case ascDischarge vts ascG ascL of
      Yes []       ->  return []
      Yes [ascL']  ->  ascsDischarge vts ascsG ascL'
      But msgs     ->  fail $ unlines msgs
\end{code}

\newpage

Finally, we get to where the real work is done.
Here we are trying to show:
\begin{equation*}
 G_i
 \vdash
 L_j \quad \where \quad i,j \in \setof{D,C,pre}
\end{equation*}
\begin{code}
ascDischarge :: MonadFail m => [VarTable]
            -> AtmSideCond -> AtmSideCond -> m [AtmSideCond]
-- ascDischarge vts ascG ascL
-- ascGVar ascG == ascGVar ascL
\end{code}

We use $V$ to denote the general variable,
which represents some set of (other) variables.
We have a situation where we may be able to discharge,
or falsify, but also have the possibility of being unable to do either.
This may result in the side-condition being retained,
perhaps ``reduced'' to some degree.
We use the notation $G \discharges L \mapsto R$
to say that $G$ being true means that we can simplify $L$ to a ``residual'' $R$.

The following cases need special treatment:
\begin{itemize}
  \item
    A translated law side-condition of the form $\emptyset \supseteq v$,
    where $v$ is a standard variable.
    This is simply false.
\begin{code}
ascDischarge _ _ (CoveredBy NU  (StdVar (Vbl _ ObsV _)) dL)
  | S.null dL  =  fail ("Empty set cannot cover a standard obs. variable")
\end{code}
  \item
    Any occurrences of a floating variable in a translated law side-condition
    should be retained.
    We let $D_{?L}$ and $C_{?L}$ denote
    the floating subsets of $D_L$ and $C_L$ respectively.
\end{itemize}
We also need to handle cases like $O_1 \notin P$.
This reduces to $true$ because of the following things that are
true for known variables $O$ and $O'$:
\begin{equation*}
   O \cup O' \supseteq P
\qquad O \disj O'
\qquad O \disj O_n
\qquad O' \disj O_n
\end{equation*}
The assertions $O \disj O' \quad O \disj O_n \quad O' \disj O_n$
are true because decorations ($x'~ x_n$) designate different variables.
We also need the fact $O \cup O' \supseteq P$
as a side-condition to those definitions that depend on it
(most notably, that of sequential composition).
\begin{eqnarray*}
   O \cup O' \supseteq P &\implies& O_m \disj P
\\&=& \mbox{set theory}
\\ && \true
\\
O \cup O' \supseteq V &\discharges& O_m \disj V
\end{eqnarray*}
This is subsumed by the
$C_G \supseteq V \discharges D_L \disj V $
discharge rule further below.
% \begin{code}
% ascDischarge (CoveredBy NU  (StdVar (Vbl _ PredV _)) oo'L)
%              (Disjoint NU  gv omL)
%   | isWhenPartition oo'L omL   =  return [] -- true
%   where
%     isWhenPartition oo'L omL  -- same name, partitions {Before,During,After}
%       = False -- NYI
% \end{code}

Now, we work through the combinations:
\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true, \quad\IF\quad D_L \subseteq D_G
\\ & \mapsto & (D_L\setminus D_G) \disj V
\end{eqnarray*}
\begin{code}
ascDischarge vts (Disjoint _ _ dG) (Disjoint _ gv dL)
  | dL `S.isSubsetOf` dG  =  return [] -- true
  | otherwise             =  return [Disjoint NU  gv (dL S.\\ dG)]
\end{code}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false,
     \quad\IF\quad C_L \subseteq D_G \land isStdObs(V)
\\ & \mapsto & (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
\begin{code}
ascDischarge vts (Disjoint _ _ dG) c@(CoveredBy _ gv cL)
  | cL `S.isSubsetOf` dG && isObsGVar gv  =  fail "Disj=>emptyCover"
  | otherwise                             =  return [CoveredBy NU  gv (cL S.\\ dG)]
\end{code}

\begin{eqnarray*}
   C_G \supseteq V \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad C_G \subseteq C_L
\\ & = & \false, \quad \IF \quad C_G \disj C_L \land isStdObs(V)
\\ & \mapsto & (C_G \cap C_L)\cup C_{?L} \supseteq V
\end{eqnarray*}
Here we have to ensure that $C_{?L}$ is retained, as no floating variables
exist in $C_G$, and so the intersection would remove those in $C_L$.
\begin{code}
ascDischarge vts (CoveredBy NU _ cG) (CoveredBy NU  gv cL)
  | cG `S.isSubsetOf` cL  =  return []
  | cG `disjoint` cL && isObsGVar gv  =  fail "CoverDisj=>noCover"
  | otherwise  =  return
                    [CoveredBy NU  gv ((cG `S.intersection` cL) `S.union` floatsOf cL)]
  where floatsOf = S.filter isFloatingGVar
\end{code}


\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & = & \true, \quad \IF~ C_G\cap D_L = \emptyset
\\ & \mapsto & D_L \disj V
\end{eqnarray*}
\begin{code}
ascDischarge vts (CoveredBy NU  _ cG) d@(Disjoint NU  gv dL)
  | S.null (cG `S.intersection` dL)  =  return []
  | otherwise                        =  return [d]
\end{code}


Anything else is not handled right now;
\begin{code}
ascDischarge _ _ ascL = return [ascL]
\end{code}

\subsubsection{Freshness Condition  Discharge}

We have reduced our original problem down to:
$$
 G_F
 \vdash
 \left( \bigwedge_{j \in J \subseteq\setof{1 \dots n}} L_j \land L_F  \right)
$$
The solution is
$$
\bigwedge_{j \in J' \subseteq J} L_j \land (L_F\setminus G_F)
$$
where elements of $G_F$ can be used to satisfy some $L_j$.

\begin{code}
freshDischarge :: MonadFail m => [VarTable]
              -> VarSet -> VarSet -> [AtmSideCond] -> m SideCond
freshDischarge vts anteFvs cnsqFvs asc
  = do asc' <- freshDischarge' vts anteFvs asc
       return (asc' , cnsqFvs S.\\ anteFvs )
\end{code}

\begin{code}
freshDischarge' :: MonadFail m => [VarTable]
                -> VarSet -> [AtmSideCond] -> m [AtmSideCond]
freshDischarge' vts anteFvs [] = return []
freshDischarge' vts anteFvs (asc:ascs)
  = do ascl  <- freshAtomDischarge vts anteFvs asc
       ascs' <- freshDischarge'    vts anteFvs ascs
       return (ascl++ascs')
\end{code}

We use a set of fresh variables ($G_F$)
to try to discharge an atomic side-condition ($L_j$):
$$
G_F \vdash L_j
$$
there are three possible outcomes:
\begin{description}
  \item [Contradicted]  Fail
  \item [Fully Discharged]  Return []
  \item [Not Fully Discharged]  Return [$L'_j$]
\end{description}
\begin{code}
freshAtomDischarge :: MonadFail m => [VarTable]
                   -> VarSet -> AtmSideCond -> m [AtmSideCond]
\end{code}
We now consider the following possibilities:
\begin{eqnarray*}
   G_F \discharges D_L \disj V
   &=& \true, \quad \IF\quad D_L \subseteq G_F
\\ &\mapsto& D_L \setminus G_F \disj V
\end{eqnarray*}
\begin{code}
freshAtomDischarge vts gF (Disjoint NU  gv dL)
  | dL `S.isSubsetOf` gF  =  return []
  | otherwise  =  return [Disjoint NU  gv (dL S.\\ gF)]
\end{code}

\begin{eqnarray*}
   G_F \discharges C_L \supseteq V
   &\mapsto&  C_L \setminus G_F \supseteq V
\end{eqnarray*}
\begin{code}
freshAtomDischarge vts gF (CoveredBy NU  gv cL) = return [CoveredBy NU  gv (cL S.\\ gF)]
\end{code}


Anything else is not handled right now.
\begin{code}
freshAtomDischarge vts gF asc = return [asc]
\end{code}


\newpage
\subsection{Check for Floating Conditions}

When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check that \emph{all} the atomic side-conditions in that residual
mention variables that are marked as ``floating''.
Only these can possibly be instantiated to satisfy the residual side-condition.
\begin{code}
isFloatingASC :: AtmSideCond -> Bool
isFloatingASC (SD  _ gv vs)  = isFloatingGVar gv || hasFloating vs
isFloatingASC (SS  _ gv vs)  = isFloatingGVar gv || hasFloating vs
hasFloating :: VarSet -> Bool
hasFloating vs = any isFloatingGVar $ S.toList vs
\end{code}
One exception to this, during law matching,
is that coverage may reduce to the empty set
because unbound variables given a temporary binding
to a ``?'' variable (\texttt{bindFloating})
will not cancel out other variables that they should be able to do,
if instantiated properly.
\begin{code}
tolerateAutoOrNull :: VarSet -> AtmSideCond -> Bool
tolerateAutoOrNull unbound (Disjoint NU  _ d) =  unbound `overlaps` d
tolerateAutoOrNull unbound (CoveredBy NU  _ c)   =  S.null c || unbound `overlaps` c
tolerateAutoOrNull _       _              =  False
autoOrNullInAll unbound = all (tolerateAutoOrNull unbound)
\end{code}



\newpage
\subsection{Building side-conditions.}

Simple side-condition builders.

$\lst v \disj \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  ([ Disjoint NU  tV (S.fromList vl) ], S.empty)
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  ([ CoveredBy NU  tV (S.fromList vl) ], S.empty)
\end{code}

$u,v,\dots \textbf{fresh.}$
\begin{code}
fresh :: VarSet -> SideCond
fresh fvs = ([],fvs)
\end{code}

\newpage
\subsection{Side-condition Queries}

First, given a variable-set,
return all ASCs that mention any variable in that set:
\begin{code}
citingASCs :: VarSet -> SideCond -> [AtmSideCond]
citingASCs vs (sc,_) = filter (cited vs) sc

cited :: VarSet -> AtmSideCond -> Bool
vs `cited` asc  =  vs == ascVSet asc
\end{code}

\newpage

\subsection{SideCond Tests}

Variable Side-Condition test values:
\begin{code}
i_a = fromJust $ ident "a"
i_b = fromJust $ ident "b"
i_e = fromJust $ ident "e"
i_f = fromJust $ ident "f"

v_a =  PreVar    $ i_a
v_b =  PreVar    $ i_b
v_a' = PostVar   $ i_a
v_b' = PostVar   $ i_b
s_s  = StaticVar $ fromJust $ ident "s"

gv_a =  StdVar v_a
gv_b =  StdVar v_b
gv_a' = StdVar v_a'
gv_b' = StdVar v_b'
gv_s  = StdVar s_s

s0   = S.fromList [] :: VarSet
sa   = S.fromList [gv_a]
sa'  = S.fromList [gv_a']
sb   = S.fromList [gv_b]
sab  = S.fromList [gv_a,gv_b]
saa' = S.fromList [gv_a,gv_a']
sab' = S.fromList [gv_a,gv_b']
sbb' = S.fromList [gv_b,gv_b']
\end{code}

Test values:
\begin{code}
v_e  = StdVar $ PreExpr  $ i_e
v_f  = StdVar $ PreExpr  $ i_f
v_e' = StdVar $ PostExpr $ i_e
v_f' = StdVar $ PostExpr $ i_f
\end{code}


\subsubsection{Atomic Checker Tests}

\begin{code}
tst_scCheck :: TF.Test
tst_scCheck
 = testGroup "Atomic Side-Condition checker"
     [ tst_scChkDisjoint
     , tst_scChkCovers ]


tstFalse = Nothing
tstTrue  = Just Nothing
tstWhatever sc = Just $ Just sc

tst_scChkDisjoint
 = testGroup "Disjoint NU  (no known vars)"
    [ testCase "gv_a `disjoint` empty is True"
       ( ascCheck [] (Disjoint NU  gv_a S.empty) @?= tstTrue )
    , testCase "v_e `disjoint` empty is True"
       ( ascCheck [] (Disjoint NU  v_e S.empty) @?= tstTrue )
    , testCase "gv_a `disjoint` {gv_a} is False"
       ( ascCheck [] (Disjoint NU  gv_a $ S.singleton gv_a) @?= tstFalse )
    , testCase "gv_a `disjoint` {gv_b} is True"
       ( ascCheck [] (Disjoint NU  gv_a $ S.singleton gv_b) @?= tstTrue )
    , testCase "v_e `disjoint` {v_e} stands"
       ( ascCheck [] (Disjoint NU  v_e $ S.singleton v_e)
         @?= tstWhatever  (Disjoint NU  v_e $ S.singleton v_e) )
    , testCase "v_e `disjoint` {v_f} stands"
       ( ascCheck [] (Disjoint NU  v_e $ S.singleton v_f)
         @?= tstWhatever  (Disjoint NU  v_e $ S.singleton v_f) )
    , testCase "v_e `disjoint` {gv_a} stands"
       ( ascCheck [] (Disjoint NU  v_e $ S.singleton gv_a)
         @?= tstWhatever  (Disjoint NU  v_e $ S.singleton gv_a) )
    , testCase "gv_a `disjoint` {v_f} stands"
       ( ascCheck [] (Disjoint NU  gv_a $ S.singleton v_f)
         @?= tstWhatever  (Disjoint NU  gv_a $ S.singleton v_f) )
    , testCase "gv_a `disjoint` {gv_b,v_f} stands"
       ( ascCheck [] (Disjoint NU  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (Disjoint NU  gv_a $ S.fromList [gv_b,v_f]) )
    ]

tst_scChkCovers
 = testGroup "CoveredBy NU  (no known vars)"
    [ testCase "gv_a `coveredby` empty is False"
       ( ascCheck [] (CoveredBy NU  gv_a S.empty) @?= tstFalse )
    , testCase "v_e `coveredby` empty stands"
       ( ascCheck [] (CoveredBy NU  v_e S.empty)
         @?= tstWhatever (CoveredBy NU  v_e S.empty) )
    , testCase "gv_a `coveredby` {gv_a} is True"
       ( ascCheck [] (CoveredBy NU  gv_a $ S.singleton gv_a) @?= tstTrue )
    , testCase "gv_a `coveredby` {gv_b} is False"
       ( ascCheck [] (CoveredBy NU  gv_a $ S.singleton gv_b) @?= tstFalse )
    , testCase "v_e `coveredby` {v_e} is True"
       ( ascCheck [] (CoveredBy NU  v_e $ S.singleton v_e) @?= tstTrue )
    , testCase "v_e `coveredby` {v_f} stands"
       ( ascCheck [] (CoveredBy NU  v_e $ S.singleton v_f)
         @?= tstWhatever  (CoveredBy NU  v_e $ S.singleton v_f) )
    , testCase "v_e `coveredby` {gv_a} stands"
       ( ascCheck [] (CoveredBy NU  v_e $ S.singleton gv_a)
         @?= tstWhatever  (CoveredBy NU  v_e $ S.singleton gv_a) )
    , testCase "gv_a `coveredby` {v_f} stands"
       ( ascCheck [] (CoveredBy NU  gv_a $ S.singleton v_f)
         @?= tstWhatever  (CoveredBy NU  gv_a $ S.singleton v_f) )
    , testCase "gv_a `coveredby` {gv_b,v_f} stands"
       ( ascCheck [] (CoveredBy NU  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (CoveredBy NU  gv_a $ S.fromList [gv_b,v_f]) )
    ]
\end{code}

\subsubsection{Merging Tests}

\begin{code}
tst_mrgAtmCond :: TF.Test
tst_mrgAtmCond
 = testGroup "Merging Side-Conditions (no known vars)"
     [ testCase "merge gv_a `disjoint` empty  into [] is True"
        ( mrgAtmCond [] (Disjoint NU  gv_a S.empty) [] @?= Just [] )
     , testCase "merge gv_a `disjoint` {gv_a} into [] is False"
        ( mrgAtmCond [] (Disjoint NU  gv_a $ S.singleton gv_a) [] @?= Nothing )
     , testCase "merge v_e `coveredby` {v_f}  into [] is [itself]"
        ( mrgAtmCond [] (CoveredBy NU  v_e $ S.singleton v_f) []
          @?= Just [CoveredBy NU  v_e $ S.singleton v_f] )
     , testCase "merge gv_a `disjoint` empty  into [asc(gv_b)] is [asc(gv_b)]]"
        ( mrgAtmCond [] (Disjoint NU  gv_a S.empty) [asc1] @?= Just [asc1] )
     , testCase "merge gv_a `disjoint` {gv_a} into [asc(gv_b)] is False"
        ( mrgAtmCond [] (Disjoint NU  gv_a $ S.singleton gv_a) [asc1] @?= Nothing )
     , testCase
        "merge v_e `coveredby` {v_f}  into [asc(gv_b)] is [asc(gv_b),itself]"
        ( mrgAtmCond [] (CoveredBy NU  v_e $ S.singleton v_f) [asc1]
          @?= Just [asc1,CoveredBy NU  v_e $ S.singleton v_f] )
     ]

asc1 = (CoveredBy NU  gv_b $ S.fromList [gv_b,v_f])
\end{code}

\subsubsection{Discharge Tests}

\begin{code}
tst_ascDischarge :: TF.Test
tst_ascDischarge
 = testGroup "Discharging Side-Conditions"
     [ test_DisjDischarge
     ]
\end{code}


\begin{code}
test_DisjDischarge
  = testGroup "Disjoint NU  discharges ..."
      [ testCase "1+1=2" ( 1+1 @?= 2)
      ]
\end{code}


\subsubsection{Exported Test Group}

\begin{code}
int_tst_SideCond :: [TF.Test]
int_tst_SideCond
  = [ testGroup "\nSideCond Internal"
       [ tst_scCheck
       , tst_mrgAtmCond
       -- , tst_ascDischarge
       ]
    ]
\end{code}
