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
\begin{code}
type SideCond = [AtmSideCond] -- [] is "true"
\end{code}
An atomic condition can have the form:
\begin{eqnarray*}
   x,\lst v   \notin  \fv(T)
   && \mbox{disjoint, short for }\{x,\lst v\} \cap \fv(T) = \emptyset
\\ x,\lst v      =    \fv(T) && \mbox{exact}
\\ x,\lst v \supseteq \fv(T) && \mbox{covering}
\\ pre      \supseteq \fv(T) && \mbox{pre-condition, no dashed variables}
\end{eqnarray*}
In most cases the term $T$ will be very general,
and will be represented by a variable.
In some cases, we will use a list-variable to denoted a list of terms,
usually expressions, and we will expect there to be only one general variable
which will itself be a list variable:
\begin{eqnarray*}
   \lst v   \notin  \fv(\lst e) && \mbox{disjoint, short for }
   v_1\notin \fv(e_1) \land \dots \land v_n\notin \fv(e_n)
\\ \lst v      =    \fv(\lst e) && \mbox{exact, short for }
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
will introduce a proof-local goal side-condition that $\lst x = \fv(T)$.
However, a match against the rhs,
where $\lst x$ is bound to variable collection $V$ (say),
will require the goal to have a side condition that implies
the non-existential condition $V \supseteq \fv(T)$.

\subsection{Atomic Side-Conditions}

We now introduce our notion of an atomic-side condition.
\begin{code}
data AtmSideCond
 = SD  GenVar VarSet -- Disjoint
 | SE  GenVar VarSet -- Equals
 | SS  GenVar VarSet -- Superset (covers)
 | ESS GenVar VarSet -- Exists Superset (covers)
 | SP  GenVar        -- Pre
 deriving (Eq,Ord,Show,Read)

pattern Disjoint gv vs = SD  gv vs  --  vs `intersect`  gv = {}
pattern Exact    gv vs = SE  gv vs  --  vs      =       gv
pattern Covers   gv vs = SS  gv vs  --  vs `supersetof` gv
pattern ExCover  gv vs = ESS gv vs  --  exists vs `supersetof` gv
pattern IsPre    gv    = SP  gv
\end{code}

Sometimes we want the \texttt{GenVar} component,
\begin{code}
ascGVar :: AtmSideCond -> Maybe GenVar
ascGVar (Disjoint gv _)  =  Just gv
ascGVar (Exact    gv _)  =  Just gv
ascGVar (Covers   gv _)  =  Just gv
ascGVar (ExCover  gv _)  =  Just gv
ascGVar (IsPre    gv)    =  Just gv
\end{code}
or the \texttt{VarSet} part:
\begin{code}
ascVSet :: AtmSideCond -> Maybe VarSet
ascVSet (Disjoint _ vs)  =  Just vs
ascVSet (Exact    _ vs)  =  Just vs
ascVSet (Covers   _ vs)  =  Just vs
ascVSet (ExCover  _ vs)  =  Just vs
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

Merging side-conditions is tricky,
mainly because we have 6 variants giving us 21 combinations,
allowing for symmetry.
1 variant (freshness), has no associated general variable,
so applies universally.
The others only interact when associated with the same general variable.

We support only one way to assemble a side-condition from atomic ones.
This uses 5 functions to do the work, one for each atomic variant.
\begin{code}
mrgAtmCond :: Monad m => AtmSideCond -> SideCond -> m SideCond
mrgAtmCond (IsPre    gv)    ascs
  =  splice (mrgIsPre gv) $ brkspn (cites gv) ascs
mrgAtmCond (Disjoint gv vs) ascs
  =  splice (mrgDisjoint gv vs) $ brkspn (cites gv) ascs
mrgAtmCond (Exact    gv vs) ascs
  =  splice (mrgExact gv vs) $ brkspn (cites gv) ascs
mrgAtmCond (Covers   gv vs) ascs
  =  splice (mrgCovers gv vs) $ brkspn (cites gv) ascs

cites gv (IsPre    gv')    =  gv == gv'
cites gv (Disjoint gv' _)  =  gv == gv'
cites gv (Exact    gv' _)  =  gv == gv'
cites gv (Covers   gv' _)  =  gv == gv'
cites gv (ExCover  gv' _)  =  gv == gv'

brkspn :: (a -> Bool) -> [a] -> ([a], [a], [a])
brkspn p xs = let
                (before,rest) = break p xs
                (found,after) = span  p rest
              in (before,found,after)

splice mrg (before,found,after)
  = do found' <- mrg found
       return (before++found'++after)
\end{code}

Merging two side-conditions is then straightforward:
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

An assertion $a$ is a term/side-condition pair $(t,sc)$.
Consider that case of matching a candidate term and side-condition
$a_C =(t_C,sc_C)$
against a pattern term and side-conditions
$a_P =(t_P,sc_P)$.
Once we have a binding $\beta$,
we can apply it to the pattern side-condition
to translate it into candidate ``space'':
$$
sc_{P'} = \beta(sc_P).
$$
In order to discharge the pattern side-condition,
we must prove that the candidate side-conditions
are sufficient to infer the translated version
of the candidate side-condition:
$$
sc_C \implies sc_{P'}.
$$
In general, the candidate term $t_C$ will be a sub-part
(the ``focus'')
of a larger goal term $t_G$,
and the pattern $t_P$ may be part of a complete law $t_L$
(e.g., one side of an equivalence).
This can mean that sometimes we need to take this larger
context in mind.
This can mean that the binding returned by matching is
incomplete and needs to be augmented in this larger context.

For example, a pattern freshness side-condition for $v$
requires ensuring that the binding for $v$
maps to something that is not free in $t_G$.
Another example is the need for existential side-conditions
already discussed above.

So the overall matching process is,
given $t_C$ and $t_P$ chosen from $t_G$ and $t_L$:
\begin{enumerate}
  \item match $t_C$ against $t_P$ to obtain binding $\beta_1$;
  \item complete bindings in the overall contexts
    determined by $a_G$ and $a_L$ to get $\beta_2$;
  \item compute $sc_{P'}=\beta_2(sc_P)$;
  \item check validity of $sc_C \implies sc_{P'}$;
  \item return $\beta_2$ as final result.
\end{enumerate}


\textbf{
NOTE: this is not right at present.
We need to handle the presence of pattern variables in the replaceent term
that where not in a (partially) match pattern.
The variables wil not having any binding.
We want to instantiate those in a way that maximises the chance of
discharging any side condition.
}


We want to determine if one side-condition implies another.
We have something of the form:
\begin{eqnarray*}
 a_1 \land \dots \land a_m &\implies& c_1 \land \dots \land c_n
\end{eqnarray*}
where $a_i$ are the antecedent (match candidate) atomic side-conditions,
and $c_j$
are those of the consequent (match pattern mapped by match binding)
atomic side-conditions.
This corresponds to showing the validity of:
\begin{eqnarray*}
 \lnot a_1 \lor \dots \lor \lnot a_m &\lor& c_1 \land \dots \land c_n
\end{eqnarray*}
There are some obvious optimisations:
\begin{enumerate}
  \item Having $n=0$ means the consequent is true, so we are valid.
  \item Having $m=0$ means the antecedent is true,
         so requiring $n=0$ for validity to hold.
  \item Having $a_i=c_j$ means that we can remove $c_j$
  \item Having $a_i \implies c_j$ means that we can remove $c_j$.
  \item Having $a_i \implies \lnot c_j$ means that we cannot be valid.
  \item If there is no $a_i$ that implies a given $c_j$,
        then we cannot be valid.
\end{enumerate}
\begin{code}
scDischarged :: SideCond -> SideCond -> Bool
scDischarged anteSC []      =  True                               -- 1 above
scDischarged []     cnsqSC  =  False                              -- 2 above
scDischarged anteSC cnsqSC  =  scDisch3 anteSC (cnsqSC \\ anteSC) -- 3 above

scDisch3     anteSC []      =  True                               -- 1,3 above
scDisch3     []     cnsqSC  =  False                              -- 2 above
scDisch3     anteSC (cnsqASC:cnsqASCs)                            -- 4-6 above
  = ascDisch456 cnsqASC anteSC
    &&
    scDisch3 anteSC cnsqASCs

ascDisch456 _ []            =  False                              -- 6 above
ascDisch456 cnsqASC (anteASC:anteASCs)
  = case ascImplies cnsqASC anteASC of
      Just b                -> b                                  -- 4,5 above
      Nothing               -> ascDisch456 cnsqASC anteASCs       -- 6 above
\end{code}

Given an $a_i$ and $c_j$, there are three possibilities of interest:
$a_i \implies c_j$, $a_i \implies \lnot c_j$, or neither of these two holds.
The first two possibilites allow \texttt{ascDisch456} to return a conclusion.
The third means we need to keep searching the $a_i$s.

We note that an \texttt{IsPre} atomic side-condition
can only imply itself,
so will have been swept up earlier by 3 above.
Any two of the remaining kinds of atomic side-condition can only interact
as per 4 or 5 above, if they have the same general variable.
\begin{code}
ascImplies :: AtmSideCond -> AtmSideCond -> Maybe Bool
ascImplies cnsqASC anteASC
 | ascGVar cnsqASC == ascGVar anteASC  =  cnsqASC `ascimp` anteASC
ascImplies _       _                   =  Nothing
\end{code}

\newpage
\subsubsection{SC Implication by cases}

Given (candidate) atomic side-condition $c$,
and (pattern) atomic side-condition $p$,
we want to know if we can assert
$$ c \implies p \qquad\textrm{or}\qquad c \implies \lnot p$$
or lack enough information to decide these.
\begin{code}
ascimp :: AtmSideCond -> AtmSideCond -> Maybe Bool
\end{code}

We assume here that $U$ is the ``universe'' of all variables
(i.e. all the variables free in the conjecture being proven).
Its occurence below means that deciding the implication
is not feasible without global knowledge
of the whole proof goal.
Note also that $v$ is a variable set in general.
We use $A \disj B$ as short for $A \cap B = \emptyset$,
and where a predicate is expected, use $A \cap B$
to denote $A \cap B \neq \emptyset$.


%% Disjoint => ...

\paragraph{Disjoint implies Disjoint}
\begin{eqnarray*}
   C \disj v \implies  P \disj v &\textrm{if}& C \supseteq P
\\ C \disj v \implies  P \cap v  && \textrm{insufficient info.}
\end{eqnarray*}
\begin{code}
(Disjoint _ vsC) `ascimp` (Disjoint _ vsP)
  |  vsP `S.isSubsetOf` vsC  =  Just True
\end{code}

\paragraph{Disjoint implies Exact}
\begin{eqnarray*}
   C \disj v \implies  P = v    && \textrm{insufficient info.}
\\ C \disj v \implies  P \neq v &\textrm{if}& C \cap P
\end{eqnarray*}
\begin{code}
(Disjoint _ vsC) `ascimp` (Exact _ vsP)
  |  vsP `overlaps` vsC  =  Just False
\end{code}

\paragraph{Disjoint implies Covers}
\begin{eqnarray*}
   C \disj v \implies  P \supseteq v     && \textrm{insufficient info.}
\\ C \disj v \implies  P \not\supseteq v && \textrm{insufficient info.}
\end{eqnarray*}


%% Exact => ...

\paragraph{Exact implies Disjoint}
\begin{eqnarray*}
   C = v \implies  P \disj v   &\textrm{if}& C \disj P
\\ C = v \implies  P \cap v    &\textrm{if}& C \cap P
\end{eqnarray*}
\begin{code}
(Exact _ vsC) `ascimp` (Disjoint _ vsP) =  Just (vsC `disjoint` vsP)
\end{code}

\paragraph{Exact implies Exact}
\begin{eqnarray*}
   C = v \implies  P = v     &\textrm{if}& C = P
\\ C = v \implies  P \neq v  &\textrm{if}& C \neq P
\end{eqnarray*}
\begin{code}
(Exact _ vsC) `ascimp` (Exact _ vsP) =  Just (vsC == vsP)
\end{code}

\paragraph{Exact implies Covers}
\begin{eqnarray*}
   C = v \implies  P \supseteq v      &\textrm{if}& C \subseteq P
\\ C = v \implies  P \not\supseteq v  &\textrm{if}& C \not\subseteq P
\end{eqnarray*}
\begin{code}
(Exact _ vsC) `ascimp` (Covers _ vsP) =  Just (vsC `S.isSubsetOf` vsP)
\end{code}


%% Covers => ...

\paragraph{Covers implies Disjoint}
\begin{eqnarray*}
   C \supseteq v \implies  P \disj v   &\textrm{if}& C \disj P
\\ C \supseteq v \implies  P \cap v    && \textrm{insufficient info.}
\end{eqnarray*}
\begin{code}
(Covers _ vsC) `ascimp` (Disjoint _ vsP)
  |  vsP `disjoint` vsC  =  Just True
\end{code}

\paragraph{Covers implies Exact}
\begin{eqnarray*}
   C \supseteq v \implies  P = v    && \textrm{insufficient info.}
\\ C \supseteq v \implies  P \neq v &\textrm{if}& C \not\supseteq P
\end{eqnarray*}
\begin{code}
(Covers _ vsC) `ascimp` (Exact _ vsP)
  |  not(vsP `S.isSubsetOf` vsC)  =  Just False
\end{code}

\paragraph{Covers implies Cover}
\begin{eqnarray*}
   C \supseteq v \implies  P \supseteq v     & \textrm{if}& C \subseteq P
\\ C \supseteq v \implies  P \not\supseteq v && \textrm{insufficient info.}
\end{eqnarray*}
\begin{code}
(Covers _ vsC) `ascimp` (Covers _ vsP)
  |  vsC `S.isSubsetOf` vsP  =  Just True
\end{code}




\begin{code}
-- Disjoint _ vs
-- Exact    _ vs
-- Covers   _ vs
-- Fresh      vs
\end{code}




Anything else results in no strong conclusion:
\begin{code}
ascimp _ _ = Nothing -- for now
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
