\section{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  AtmSideCond
, pattern Disjoint, pattern Covers, pattern IsPre
, ascGVar, ascVSet
, SideCond, scTrue
, mrgAtmCond, mrgSideCond, mkSideCond
, scDischarged
, notin, covers, pre
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

We note that disjointness and being a (pre-)condition
distribute through conjunction without restrictions,
so we have, for example, that:
\begin{eqnarray*}
   x,y \notin S,T
   &\equiv&
   x \notin S \land x \notin T \land y \notin S \land y \notin T
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

We already have to cope with $C$ matching $P$ in $P \sim R$,
where variables in $R$, but not in $P$,
are not in the resulting match-binding.
If such variables occur in side-conditions,
then we treat those variables as ``existential''.
We are free to instantiate them using variables and terms in $P$ and $R$.

\newpage
\subsection{Atomic Side-Conditions}

We now introduce our notion of an atomic-side condition.
\begin{code}
data AtmSideCond
 = SD  GenVar VarSet -- Disjoint
 | SS  GenVar VarSet -- Superset (covers)
 | SP  GenVar        -- Pre
 deriving (Eq,Ord,Show,Read)

pattern Disjoint gv vs = SD  gv vs  --  vs `intersect`  gv = {}
pattern Covers   gv vs = SS  gv vs  --  vs `supersetof` gv
pattern IsPre    gv    = SP  gv     --  gv is pre-condition
\end{code}

Sometimes we want the \texttt{GenVar} component,
\begin{code}
ascGVar :: AtmSideCond -> GenVar
ascGVar (Disjoint gv _)  =  gv
ascGVar (Covers   gv _)  =  gv
ascGVar (IsPre    gv  )  =  gv
\end{code}
or the \texttt{VarSet} part:
\begin{code}
ascVSet :: AtmSideCond -> Maybe VarSet
ascVSet (Disjoint _ vs)  =  Just vs
ascVSet (Covers   _ vs)  =  Just vs
ascVSet (IsPre    _   )  =  Nothing
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
then they are ordered as follows:
\texttt{Disjoint},
\texttt{Covers},
and \texttt{IsPre}.
We can only have at most one of each.

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
[Disjoint]  [Disjoint,Covers]  [Disjoint,IsPre]
[Disjoint,Covers,IsPre]
[Covers]    [Covers,IsPre]
[IsPre]
\end{verbatim}

\subsubsection{ASC Merge Laws}

We have the following interactions,
where $D$ and $C$ are the variable-sets found
in \texttt{Disjoint} and \texttt{Covers} respectively.
We also overload the notation to denote the corresponding condition.
So, depending on context,
$D$ can denote a variable-set
or the predicate $D \disj G$ ($G$ being the general variable in question).
\begin{eqnarray*}
   D_1 \land D_2 &=&  D_1 \cup D_2
\\ C_1 \land C_2 &=&  C_1 \cup C_2
\\ pre_1 \land pre_2 &=& pre_1
\\ D \land C
   &=&  \bot
        ~\cond{D \supseteq C}~
        D \land (C \setminus D)
\\ D \land pre &=&  D \land pre
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
scDischarged :: Monad m => SideCond -> SideCond -> m SideCond
\end{code}
We have something of the form:
$$
 \left( \bigwedge_{i \in 1 \dots m} G_i \right)
 \implies
 \left( \bigwedge_{j \in 1 \dots n} L_j \right)
$$
In our representation both the $G_i$ and $L_j$
are ordered by general variable ($V$).
So we can work through both lists,
using all the $G_i$ for a given g.v.,
to attempt to discharge all the $L_j$ for that same g.v.
Success is when all such $L_j$ groups have been shown to be $\true$.
Failure occurs if any $L_j$ group results in $\false$.
If we are left with undischarged $L_j$,
then the interpretation depends on if we are doing many matches
and displaying them, or actually trying to apply a match outcome.

We start with simple end-cases:
\begin{code}
scDischarged _ []    =  return scTrue  -- G => true   is  true
scDischarged [] scL  =  return scL     -- true => L is L,  i.e., not discharged
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
scDischarged' :: Monad m => [(GenVar,[AtmSideCond])] -> [(GenVar,[AtmSideCond])]
              -> m SideCond
scDischarged' _ []      =  return scTrue                   -- discharged
scDischarged' [] grpsL  =  return $ concat $ map snd grpsL -- not discharged
scDischarged' (grpG@(gvG,ascsG):restG) grpsL@(grpL@(gvL,ascsL):restL)
  | gvG < gvL  =  scDischarged' restG grpsL -- grpG not needed
  | gvG > gvL  =  do -- nothing available to discharge grpL
                     rest' <- scDischarged' restG restL
                     return (ascsL++rest')
  | otherwise  =  do -- use grpG to discharge grpL
                     ascs' <- grpDischarged ascsG ascsL
                     rest' <- scDischarged' restG restL
                     return (ascs'++rest')
\end{code}

We can discharge pattern side conditions under the following circumstances:
\begin{eqnarray*}
   D_G \disj V \implies D_L \disj V
   & \textbf{when} &
   D_L \subseteq D_G
\\ C_G \supseteq V \implies C_L \supseteq V
   & \textbf{when} &
   C_G \subseteq C_L
\\ C_G \supseteq V \implies D_L \disj V
   & \textbf{when} &
   C_G \disj D_L
\end{eqnarray*}
Note that knowing $D_G \disj V$
can never force us to conclude that $C_L \supseteq V$ must be true.

We can falsify pattern side conditions under the following circumstances:
\begin{eqnarray*}
 x
\end{eqnarray*}


\begin{code}
dG `d_imp_d` dL  =  dL `S.isSubsetOf` dG
cG `c_imp_c` cL  =  cG `S.isSubsetOf` cL
cG `c_imp_d` dL  =  cG `disjoint` dL
\end{code}

\textbf{As above, we only consider \texttt{Disjoint} and \texttt{Covers}
for now.}

\begin{code}
grpDischarged :: Monad m => [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
grpDischarged [Disjoint _ dG,Covers _ cG] [Disjoint _ dL,Covers _ cL]
  | (cG `c_imp_c` cL)
    && (dG `d_imp_d` dL || cG `c_imp_d` dL)               =  return []
grpDischarged [Disjoint _ dG,Covers _ cG] [Disjoint _ dL]
  | (dG `d_imp_d` dL || cG `c_imp_d` dL)                  =  return []
grpDischarged [_,Covers _ cG] [Covers _ cL]
  | (cG `c_imp_c` cL)                                     =  return []
grpDischarged [Covers _ cG] [Disjoint _ dL,Covers _ cL]
  | (cG `c_imp_d` dL && cG `c_imp_c` cL)                  =  return []
grpDischarged [Disjoint _ dG] [Disjoint _ dL]
  | (dG `d_imp_d` dL)                                     =  return []
grpDischarged [Covers _ cG] [Disjoint _ dL]
  | (cG `c_imp_d` dL)                                     =  return []
grpDischarged [Covers _ cG] [Covers _ cL]
  | (cG `c_imp_c` cL)                                     =  return []
\end{code}

Anything else we treat as false, for now.
\begin{code}
grpDischarged _ _ = fail "grpDischarged NYfI"
\end{code}

\newpage
\subsection{Building side-conditions.}

Simple side-condition builders.

$\lst v \notin \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  [ Disjoint tV (S.fromList vl) ]
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  [ Covers tV (S.fromList vl) ]
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
