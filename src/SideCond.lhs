\section{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  SideCond, AtmSideCond
, pattern Disjoint, pattern Exact
, pattern Covers, pattern ExCover
, pattern IsPre
, ascGVar, ascVSet
, scTrue, mrgSideCond
, scDischarged
, notin, is, covers, exCover, pre
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

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}


\newpage
\subsection{Introduction}

A side-condition is a property used in laws,
typically putting a constraint on the free variables of some term.
In many logics, these can be checked by simple inspection of a term.
However,
given a logic like ours with explict expression and predicate
(a.k.a. \emph{schematic}) variables this is not always possible.

A side condition is about a relationship between the free variables
of term ($T$),
and a set of other (general) variables ($x,\lst{v}$).
In general with have a conjunction of atomic conditions,
but we need to be able to distinguish between no conditions (always ``true'')
and inconsistent conditions
(e.g. $x \notin \fv(T) \land x = \fv(T) $, always ``false'').
As a false side-condition means a match failure,
we do not represent them explicitly.
Instead, any operation on side-conditions that could result
in an inconsistent result should fail, gracefully.

An atomic side-condition (ASC) can have one of the following forms,
where $T$ abbreviates $\fv(T)$:
\begin{eqnarray*}
   x,\lst v   \notin  T
   && \mbox{disjoint, short for }\{x,\lst v\} \cap \fv(T) = \emptyset
\\ x,\lst v \supseteq T && \mbox{covering}
\\ pre      \supseteq T && \mbox{pre-condition, no dashed variables}
\end{eqnarray*}
In most cases the term $T$ will be very general,
and will be represented by a variable.
In some cases, we will use a list-variable to denoted a list of terms,
usually expressions, and we will expect there to be only one general variable
which will itself be a list variable:
\begin{eqnarray*}
   \lst v   \notin  \lst e && \mbox{disjoint, short for }
   v_1\notin \fv(e_1) \land \dots \land v_n\notin \fv(e_n)
\\ \lst v      =    \lst e && \mbox{exact, short for }
   \{v_1\}= \fv(e_1) \land \dots \land \{v_n\} =  \fv(e_n)
\end{eqnarray*}
This arises when we have side-conditions between lists of variables
and expressions that occur in substitutions.

To handle certain cases, particularly to do with predicate closure operators,
we need to introduce the notion of existential side-conditions.
For example, universal closure is typically defined as
$$
  [P] \defs \forall \lst x \bullet P, \quad \lst x\supseteq P
$$
However we have theorems about universal closure
that have no such side-condition, such as
$$
 [[P]] \equiv [P]
$$
or
$$
  [P \land Q] \equiv [P] \land [Q]
$$
We cannot match any instance of universal closure above
against the definition as we cannot discharge the side-condition.
The trick is to have a special \emph{existential} side-condition,
that can be instantiated during a proof,
and discarded once the proof is complete.
$$
  [P] \defs \forall \lst x \bullet P, \quad \exists\lst x\supseteq P
$$
The basic rule is that a match against the LHS here,
where $P$ is bound to some predicate term $T$ (say)
will introduce a proof-local goal side-condition that $\lst x = T$.
However, a match against the rhs,
where $\lst x$ is bound to variable collection $V$ (say),
will require the goal to have a side condition that implies
the non-existential condition $V \supseteq T$.
This means we add a new form of atomoic side-condition
that is only used in proofs
\begin{eqnarray*}
   x,\lst v      =    T && \mbox{exact}
\end{eqnarray*}

\newpage
\subsection{Atomic Side-Conditions}

We now introduce our notion of an atomic-side condition.
\begin{code}
data AtmSideCond
 = SD  GenVar VarSet -- Disjoint
 | SS  GenVar VarSet -- Superset (covers)
 | SP  GenVar        -- Pre
 | ESS GenVar VarSet -- Exists Superset (covers)
 | SE  GenVar VarSet -- Equals
 deriving (Eq,Ord,Show,Read)

pattern Disjoint gv vs = SD  gv vs  --  vs `intersect`  gv = {}
pattern Covers   gv vs = SS  gv vs  --  vs `supersetof` gv
pattern IsPre    gv    = SP  gv     --  gv is pre-condition
pattern ExCover  gv vs = ESS gv vs  --  exists vs `supersetof` gv
pattern Exact    gv vs = SE  gv vs  --  vs      =       gv
\end{code}

Sometimes we want the \texttt{GenVar} component,
\begin{code}
ascGVar :: AtmSideCond -> Maybe GenVar
ascGVar (Disjoint gv _)  =  Just gv
ascGVar (Covers   gv _)  =  Just gv
ascGVar (IsPre    gv)    =  Just gv
ascGVar (ExCover  gv _)  =  Just gv
ascGVar (Exact    gv _)  =  Just gv
\end{code}
or the \texttt{VarSet} part:
\begin{code}
ascVSet :: AtmSideCond -> Maybe VarSet
ascVSet (Disjoint _ vs)  =  Just vs
ascVSet (Covers   _ vs)  =  Just vs
ascVSet (ExCover  _ vs)  =  Just vs
ascVSet (Exact    _ vs)  =  Just vs
ascVSet _                =  Nothing -- IsPre
\end{code}


We will want to merge a set with a maybe-set below:
\begin{code}
mrgm :: (a -> a -> a) -> a -> Maybe (a) -> a
mrgm op s Nothing    =  s
mrgm op s (Just s')  =  s `op` s'
\end{code}

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

gv_a =  StdVar v_a
gv_b =  StdVar v_b
gv_a' = StdVar v_a'
gv_b' = StdVar v_b'

s0   = S.fromList [] :: VarSet
sa   = S.fromList [gv_a]
sa'  = S.fromList [gv_a']
sb   = S.fromList [gv_b]
sab  = S.fromList [gv_a,gv_b]
saa' = S.fromList [gv_a,gv_a']
sab' = S.fromList [gv_a,gv_b']
sbb' = S.fromList [gv_b,gv_b']
\end{code}


\newpage
\subsection{Full Side Conditions}

A ``full'' side-condition is basically a list of ASCs,
interpreted as their conjunction.
\begin{code}
type SideCond = [AtmSideCond] -- all must be true
\end{code}

If the atomic condition list is empty,
then we have the trivial side-condition, which is always true:
\begin{code}
scTrue :: SideCond
scTrue = []
\end{code}

Test values:
\begin{code}
v_e  = StdVar $ PreExpr  $ i_e
v_f  = StdVar $ PreExpr  $ i_f
v_e' = StdVar $ PostExpr $ i_e
v_f' = StdVar $ PostExpr $ i_f
\end{code}

\subsection{Merging Side-Conditions}

The list of ASCs
is kept ordered by the \texttt{GenVar} component,
If there is more than one ASC with the same general variable,
then they do not contain \texttt{Exact}, and are ordered as follows:
\texttt{Disjoint},
\texttt{Covers},
\texttt{ExCover},
and \texttt{IsPre}.
We can only have at most one of each, and only one of either \texttt{Covers}
and \texttt{ExCover}.
If we have an instance of \texttt{Exact}, then all the others
are redundant.
When it comes to discharging side-conditions we shall see that \texttt{Exact}
only occurs on the candidate side, and that \texttt{ExCover} is not used.

The function \texttt{mrgAtmCond} below is the ``approved'' way
to generate side-conditions,
by merging them in, one at a time,
into a pre-existing list ordered and structured as described above.
\begin{code}
mrgAtmCond :: Monad m => AtmSideCond -> SideCond -> m SideCond
\end{code}

1st ASC is easy:
\begin{code}
mrgAtmCond asc [] = return [asc]
\end{code}

Subsequent ones mean searching to see if there are already ASCs with the
same general-variable:
\begin{code}
mrgAtmCond asc ascs = splice (mrgAtmAtms asc) $ brkspnBy (compareGV asc) ascs

compareGV asc1 asc2  =  ascGVar asc1 `compare` ascGVar asc2
sameGV asc1 asc2     =  asc1 `compareGV` asc2 == EQ
\end{code}

Now, merging an ASC in with other ASCs referring to the same general variable:
\begin{code}
mrgAtmAtms :: Monad m => AtmSideCond -> [AtmSideCond] -> m [AtmSideCond]
mrgAtmAtms asc [] = return [asc] -- it's the first.
\end{code}

Given one or more pre-existing ASCs for this g.v., we note the following possible
patterns:
\begin{verbatim}
[Exact]
[Disjoint]  [Disjoint,Covers]  [Disjoint,ExCovers]  [Disjoint,IsPre]
[Disjoint,Covers,IsPre]        [Disjoint,ExCovers,IsPre]
[Covers]    [Covers,IsPre]
[ExCover]   [ExCover,IsPre]
[IsPre]
\end{verbatim}
\begin{code}
mrgAtmAtms asc ascs = return (asc:ascs) -- for now
\end{code}

Merging two side-conditions is then straightforward,
simply merge each ASC from the one into the other,
one at a time.
\begin{code}
mrgSideCond :: Monad m => SideCond -> SideCond -> m SideCond
mrgSideCond ascs1 [] = return ascs1
mrgSideCond ascs1 (asc:ascs2)
     = do ascs1' <- mrgAtmCond asc ascs1
          mrgSideCond ascs1' ascs2
\end{code}

The tricky part is merging atomic side-conditions into a sequence
of them.

Freshness will get done, when needed
\begin{code}
mrgFresh       vs ascs            =  fail "mrgFresh NYI"
\end{code}

Here, \texttt{found} is all atomic side conditions
that refer to \texttt{gv}.


Is a (pre-)Condition will get done, when needed
\begin{code}
mrgIsPre    gv    found  =  fail "mrgIsPre NYI"
\end{code}

\begin{eqnarray*}
   D_1 \land D_2 &=&  D_1 \cup D_2
\\ D_1 \land C_2 &=&  D_1 \land C_2 \setminus D_1
\\ D_1 \land X_2 &=&  D_1 \land X_2 \cond{~D_1 \cap X_2 = \emptyset~} \bot
\\ D_1 \land pre &=&  D_1 \land pre
\end{eqnarray*}
\begin{code}
mrgDisjoint gv vs [] = return [ Disjoint gv vs ]
mrgDisjoint gv vs1 (Disjoint _ vs2 : ascs)
  = do let vs' = vs1 `S.union` vs2
       mrgDisjoint gv vs' ascs
mrgDisjoint gv vs (_: ascs) = fail "mrgDisjoint NYfI"
\end{code}

Exactness will get done, when needed
\begin{code}
mrgExact    gv vs found  =  fail "mrgExact NYI"
\end{code}

Covering will get done, when needed
\begin{code}
mrgCovers   gv vs found  =  fail "mrgCovers NYI"
\end{code}

\begin{code}
\end{code}
Easy cases first --- merging same
\begin{code}
-- mrgAtmAtm (Fresh vs1) (Fresh vs2) = return (True,Fresh (vs1 `S.union` vs2))
-- mrgAtmAtm (IsPre gv1) a@(IsPre gv2)
--  | gv1 == gv2  = return (True, a)
-- mrgAtmAtm (Disjoint gv1 vs1) (Disjoint gv2 vs2)
--  | gv1 == gv2  = return (True, Disjoint gv2 (vs1 `S.union` vs2))
-- mrgAtmAtm (Exact gv1 vs1) a@(Exact gv2 vs2)
--  | gv1 == gv2 = if vs1 == vs2
--                 then return (True, a )
--                 else fail "inconsistent exact side-cond."
-- mrgAtmAtm (Covers gv1 vs1) (Covers gv2 vs2)
--  | gv1 == gv2  = return (True, Covers gv2 (vs1 `S.intersection` vs2))
\end{code}

\newpage
\subsection{Discharging Side-conditions}

Here we simply check validity of $sc'_C \implies sc'_P$,
where $sc'_C$ is the candidate side-condition,
and $sc'_P$ is the pattern side-condition translated into candidate ``space''
after a succesful match.
\begin{code}
scDischarged :: SideCond -> SideCond -> Bool
\end{code}
We have something of the form:
$$
 \left( \bigwedge_{i \in 1 \dots m} C_i \right)
 \implies
 \left( \bigwedge_{j \in 1 \dots n} P_j \right)
$$
We want to partition both the $C_i$ and the $P_j$
based on the general variables they contain,
and handle each seperately.
Assume we have such a partition, for general variable $P$,
giving us:
$$
 \left( \bigwedge_{k \in 1 \dots p} X_k \mathcal{R}_k P \right)
 \implies
 \left( \bigwedge_{\ell \in 1 \dots q} Y_\ell  \mathcal{R}_\ell P \right)
 ,
 \qquad
 \mathcal{R}_k\in \setof{\supseteq,\disj,=},
 \mathcal{R}_\ell \in \setof{\supseteq,\disj}
$$
We can simplify $\bigwedge_{k \in 1 \dots p} X_k \mathcal{R}_k P$
and $\bigwedge_{\ell \in 1 \dots q} Y_\ell  \mathcal{R}_\ell P$ independently
to obtain, in each case, something of the form
of either $E = P$, or  $F \supseteq P \land G \disj P$,
for appropriate variable-sets $E$, $F$, and $G$.

\begin{code}
scDischarged anteSC cnsqSC
  = scDischarged' $ collateSC anteSC cnsqSC

collateSC anteSC cnsqAC
 = mergeSC (groupBy sameGV anteSC) (groupBy sameGV cnsqAC)

mergeSC anteSCg cnsqSCg = zip anteSCg cnsqSCg -- for now

scDischarged' scGroups = False -- for now
\end{code}


\begin{code}
ascImplies :: AtmSideCond -> AtmSideCond -> Maybe Bool
ascImplies cnsqASC anteASC
 | ascGVar cnsqASC == ascGVar anteASC  =  cnsqASC `ascimp` anteASC
ascImplies _       _                   =  Nothing
\end{code}

\newpage
\subsubsection{SC Implication by cases}

We use $P$ to denote the common general variable,
and the $X$ and $Y$ denote respectively the candidate and pattern variable-sets.
We note also that the identity side-condition $X=P$ can only occur
on the candidate side.
For now we do not handle pre-condition side-conditions (\texttt{IsPre}).
\begin{eqnarray*}
   X \supseteq P \implies Y \supseteq P
   &\leadsto&
   \true ~\cond{~X \supseteq Y~}~ ?
\\ X \supseteq P \implies Y \disj P
   &\leadsto&
   \false ~\cond{~Y \supseteq X~}~ ?
\\ X \disj P \implies Y \supseteq P
   &\leadsto&
   \false ~\cond{~X \supseteq Y~}~ ?
\\ X \disj P \implies Y \disj P
   &\leadsto&
   \true  ~\cond{~X \supseteq Y~}~ ?
\\ X = P \implies Y \supseteq P
   &\equiv&
   Y \supseteq X
\\ X = P \implies Y \disj P
   &\equiv&
   Y \disj X
\end{eqnarray*}
\begin{code}
ascimp :: AtmSideCond -> AtmSideCond -> Maybe Bool
\end{code}


\begin{eqnarray*}
   X \supseteq P \implies Y \supseteq P
   &\leadsto&
   \true ~\cond{~Y \subseteq X~}~ ?
\end{eqnarray*}
\begin{code}
(Covers _ vsX) `ascimp` (Covers _ vsY) | vsY `S.isSubsetOf` vsX = Just True
\end{code}

\begin{eqnarray*}
   X \supseteq P \implies Y \disj P
   &\leadsto&
   \false ~\cond{~X \subseteq Y~}~ ?
\end{eqnarray*}
\begin{code}
(Covers _ vsX) `ascimp` (Disjoint _ vsY) | vsX `S.isSubsetOf` vsY = Just False
\end{code}

\begin{eqnarray*}
   X \disj P \implies Y \supseteq P
   &\leadsto&
   \false ~\cond{~Y \subseteq X~}~ ?
\end{eqnarray*}
\begin{code}
(Disjoint _ vsX) `ascimp` (Covers _ vsY) | vsY `S.isSubsetOf` vsX = Just False
\end{code}


\begin{eqnarray*}
   X \disj P \implies Y \disj P
   &\leadsto&
   \true  ~\cond{~Y \subseteq X~}~ ?
\end{eqnarray*}
\begin{code}
(Disjoint _ vsX) `ascimp` (Disjoint _ vsY) | vsY `S.isSubsetOf` vsX = Just True
\end{code}

\begin{eqnarray*}
   X = P \implies Y \supseteq P
   &\equiv&
   X \subseteq Y
\end{eqnarray*}
\begin{code}
(Exact _ vsX) `ascimp` (Covers _ vsY) =  Just (vsX `S.isSubsetOf` vsY)
\end{code}

\begin{eqnarray*}
   X = P \implies Y \disj P
   &\equiv&
   Y \disj X
\end{eqnarray*}
\begin{code}
(Exact _ vsX) `ascimp` (Disjoint _ vsY) =  Just (vsX `disjoint` vsY)
\end{code}


Anything else results in no strong conclusion:
\begin{code}
_ `ascimp`_  =  Nothing
\end{code}

\newpage
\subsection{Building side-conditions.}

Simple side-condition builders.

$\lst v \notin \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  [ Disjoint tV (S.fromList vl) ]
\end{code}

$\lst v = \fv(T)$
\begin{code}
is :: VarList -> GenVar -> SideCond
vl `is` tV  =  [ Exact tV (S.fromList vl) ]
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  [ Covers tV (S.fromList vl) ]
\end{code}

$\exists\lst v \supseteq \fv(T)$
\begin{code}
exCover :: VarList -> GenVar -> SideCond
vl `exCover` tV  =  [ ExCover tV (S.fromList vl) ]
\end{code}

$pre \supseteq \fv(T)$
\begin{code}
pre :: GenVar -> SideCond
pre tV  = [ IsPre tV ]
\end{code}

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_SideCond :: [TF.Test]
int_tst_SideCond
  = [ testGroup "\nSideCond Internal" [] ]
--      [ varSCTests
--      , sidecondTests
--      ]
--    ]
\end{code}
