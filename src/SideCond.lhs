\section{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  AtmSideCond
, pattern Disjoint, pattern Exact
, pattern Covers, pattern ExCover
, pattern IsPre
, ascGVar, ascVSet
, SideCond, scTrue
, mrgAtmCond, mrgSideCond, mkSideCond
, scDischarged
, notin, is, covers, exCover, pre
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
ascGVar :: AtmSideCond -> GenVar
ascGVar (Disjoint gv _)  =  gv
ascGVar (Covers   gv _)  =  gv
ascGVar (IsPre    gv)    =  gv
ascGVar (ExCover  gv _)  =  gv
ascGVar (Exact    gv _)  =  gv
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

\newpage
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

\subsubsection{Merging one ASC with relevant others}

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

\subsubsection{ASC Merge Laws}

We have the following interactions,
where $D$, $C$, and $X$ are the variable-sets found
in \texttt{Disjoint}, \texttt{Covers} and \texttt{Exact} respectively.
We also overload the notation to denote the corresponding condition.
So, depending on context,
$D$ can denote a variable-set
or the predicate $D \disj P$ ($P$ being the general variable in question).
\begin{eqnarray*}
   D_1 \land D_2 &=&  D_1 \cup D_2
\\ C_1 \land C_2 &=&  C_1 \cup C_2
\\ X_1 \land X_2 &=&  X_1 ~\cond{X_1=X_2}~ \bot
\\ pre_1 \land pre_2 &=& pre_1
\\ D \land C
   &=&  \bot
        ~\cond{D \supseteq C}~
        D \land (C \setminus D)
\\ D \land X &=&  X ~\cond{D \disj X}~ \bot
\\ D \land pre &=&  D \land pre
\\ C \land X &=&  X ~\cond{C \supseteq X}~ \bot
\\ C \land pre &=&  C \land pre
\end{eqnarray*}


\subsubsection{Merging \texttt{Disjoint} in}

\begin{code}
mrgAtmAtms (Disjoint gv d0) [Disjoint _ d1,Covers _ c]
 | c `S.isSubsetOf` d'  =  fail "Disjoint covers superset"
 | otherwise            =  return [Disjoint gv d',Covers gv (c S.\\ d')]
 where d' = d0 `S.union` d1
mrgAtmAtms (Disjoint gv d0) [Disjoint _ d1]
                  =  return [Disjoint gv (d0 `S.union` d1)]
mrgAtmAtms (Disjoint gv d) [Covers _ c]
 | c `S.isSubsetOf` d  =  fail "Disjoint covers superset"
 | otherwise           =  return [Disjoint gv d,Covers gv (c S.\\ d)]
\end{code}

\subsubsection{Merging \texttt{Covers} in}

\begin{code}
mrgAtmAtms (Covers gv c0) [Disjoint _ d,Covers _ c1]
 | c' `S.isSubsetOf` d  =  fail "Superset covered by disjoint"
 | otherwise            =  return [Disjoint gv d,Covers gv (c' S.\\ d)]
 where c' = c0 `S.union` c1
mrgAtmAtms (Covers gv c) [Disjoint _ d]
 | c `S.isSubsetOf` d  =  fail "Superset covered by disjoint"
 | otherwise           =  return [Disjoint gv d,Covers gv (c S.\\ d)]
mrgAtmAtms (Covers gv c0) [Covers _ c1]
               =  return [Covers gv (c0 `S.union` c1)]
\end{code}

\textbf{For now, we only consider \texttt{Disjoint} and \texttt{Covers}.}
Every other case:
\begin{code}
mrgAtmAtms asc ascs = fail "mrgAtmAtms: NYFI"
\end{code}

\subsubsection{Merging Full Side-conditions}

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

\subsection{From ASC-list to Side-Condition}

\begin{code}
mkSideCond :: Monad m => [AtmSideCond] -> m SideCond
mkSideCond [] = return []
mkSideCond (asc:ascs)
 = do sc <- mkSideCond ascs
      mrgAtmCond asc sc
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
In our representation both the $C_i$ and $P_j$
are ordered by general variable.
So we can work through both lists,
using all the $C_i$ for a given g.v.,
to attempt to discharge all the $P_j$ for that same g.v.
Success is when all such $P_j$ groups have been shown to be $\true$.
Failure occurs if any $P_j$ group results in $\false$,
or results in some ASCs remaining.

We start with simple end-cases:
\begin{code}
scDischarged _ []  =  True   -- C => true   is  true
scDischarged [] _  =  False  -- true => P   is  P,  i.e., not discharged
\end{code}
\begin{code}
scDischarged anteSC cnsqSC
  = scDischarged' (groupByGV anteSC) (groupByGV cnsqSC)
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

Now onto processing those groups:
\begin{code}
scDischarged' :: [(GenVar,[AtmSideCond])] -> [(GenVar,[AtmSideCond])] -> Bool
scDischarged' _ []  =  True   -- see scDischarged above
scDischarged' [] _  =  False  -- see scDischarged above
scDischarged' (grpC@(gvC,ascsC):restC) grpsP@(grpP@(gvP,ascsP):restP)
  | gvC > gvP  =  False -- nothing available to discharge grpP
  | gvC < gvP  =  scDischarged' restC grpsP -- grpC not needed
  | otherwise  =  grpDischarged ascsC ascsP && scDischarged' restC restP
\end{code}

We can discharge pattern side conditions under the following
circumstances:
\begin{eqnarray*}
   D_C \disj P \implies D_P \disj P
   & \textbf{when} &
   D_P \subseteq D_C
\\ C_C \supseteq P \implies C_P \supseteq P
   & \textbf{when} &
   C_C \subseteq C_P
\\ C_C \supseteq P \implies D_P \disj P
   & \textbf{when} &
   C_C \disj D_P
\end{eqnarray*}
Note that knowing $D_C \disj P$
can never force us to conclude that $C_P \supseteq P$ must be true.

\begin{code}
dC `d_imp_d` dP  =  dP `S.isSubsetOf` dC
cC `c_imp_c` cP  =  cC `S.isSubsetOf` cP
cC `c_imp_d` dP  =  cC `disjoint` dP
\end{code}

\textbf{As above, we only consider \texttt{Disjoint} and \texttt{Covers}
for now.}

\begin{code}
grpDischarged [Disjoint _ dC,Covers _ cC] [Disjoint _ dP,Covers _ cP]
  = (cC `c_imp_c` cP) && (dC `d_imp_d` dP || cC `c_imp_d` dP)
grpDischarged [Disjoint _ dC,Covers _ cC] [Disjoint _ dP]
  = (dC `d_imp_d` dP || cC `c_imp_d` dP)
grpDischarged [_,Covers _ cC] [Covers _ cP]
  = (cC `c_imp_c` cP)
grpDischarged [Covers _ cC] [Disjoint _ dP,Covers _ cP]
  = (cC `c_imp_d` dP && cC `c_imp_c` cP)
grpDischarged [Disjoint _ dC] [Disjoint _ dP]
  = (dC `d_imp_d` dP)
grpDischarged [Covers _ cC] [Disjoint _ dP]
  = (cC `c_imp_d` dP)
grpDischarged [Covers _ cC] [Covers _ cP]
  = (cC `c_imp_c` cP)
\end{code}

Anything else we treat as false.
\begin{code}
grpDischarged _ _ = False
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
\subsection{Side-condition Queries}

First, given a variable-set,
return all ASCs that mention any variable in that set:
\begin{code}
citingASCs :: VarSet -> SideCond -> [AtmSideCond]
citingASCs vs sc = filter (cited vs) sc

cited :: VarSet -> AtmSideCond -> Bool
vs `cited` asc
  = case ascVSet asc of
      Nothing   ->  False
      Just vs'  ->  vs == vs'
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
