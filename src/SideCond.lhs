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
, scDischarge, checkUnboundInvolved
, notin, covers, pre
, citingASCs
, Assertion
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

-- import Test.HUnit
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
Exploring proofs of the above by hand reveals the importance
of being able to determine, at proof-time,
if a predicate $P$ is closed ($\emptyset \supseteq P$).


We have to cope with $C$ matching $P$ in $P \sim R$,
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
\end{code}
In the \texttt{SD} case, having an empty set reduces to \true,
while in the \texttt{SS} case,
we have an assertion that the term denoted by the general variable is closed.
\begin{code}
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
So the semantics of the disjoint ($D$) and covering ($C$) variable-sets,
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
   \sem{D_1}_G \land \sem{D_2}_g &=&  \sem{D_1 \cup D_2}_G
\\ \sem{C_1}_G \land \sem{C_2}_G &=&  \sem{C_1 \cap C_2}_G
\\ \sem{D}_G \land \sem{C}_G
   &=&  \sem{D}_G \land \sem{C \setminus D}_G
\\ &=& \sem{C \setminus D}_G, \quad \IF \quad C\setminus D = \emptyset
\\ &=& \fv.G = \emptyset \quad \IF \quad C\setminus D = \emptyset
\end{eqnarray*}
We not that an apparent contradiction between $D$ and $C$ (when $D \supseteq C$)
becomes and assertion that $G$ is closed
for any given general variable $G$,
we will have that $D$ and $C$ are disjoint.

Below, we overload the notation to denote the corresponding condition.
So, for example, depending on context,
$D$ can denote a variable-set
or the predicate $D \disj G$ ($G$ being the general variable in question).


\newpage
\subsubsection{Merging \texttt{Disjoint} into ASC}

\begin{code}
mrgAtmAtms (Disjoint gv d0) [Disjoint _ d1,Covers _ c]
 | c `S.isSubsetOf` d'  =  return [Covers gv S.empty]
 | otherwise            =  return [Disjoint gv d',Covers gv (c S.\\ d')]
 where d' = d0 `S.union` d1
mrgAtmAtms (Disjoint gv d0) [Disjoint _ d1]
                  =  return [Disjoint gv (d0 `S.union` d1)]
mrgAtmAtms (Disjoint gv d) [Covers _ c]
 | c `S.isSubsetOf` d  =  return [Covers gv S.empty]
 | otherwise           =  return [Disjoint gv d,Covers gv (c S.\\ d)]
\end{code}

\subsubsection{Merging \texttt{Covers} into ASC}

\begin{code}
mrgAtmAtms (Covers gv c0) [Disjoint _ d,Covers _ c1]
 | c' `S.isSubsetOf` d  =  return [Covers gv S.empty]
 | otherwise            =  return [Disjoint gv d,Covers gv (c' S.\\ d)]
 where c' = c0 `S.union` c1
mrgAtmAtms (Covers gv c) [Disjoint _ d]
 | c `S.isSubsetOf` d  =  return [Covers gv S.empty]
 | otherwise           =  return [Disjoint gv d,Covers gv (c S.\\ d)]
mrgAtmAtms (Covers gv c0) [Covers _ c1]
               =  return [Covers gv (c0 `S.intersection` c1)]
\end{code}

\subsubsection{Merging \texttt{IsPre} into ASC}
\begin{code}
mrgAtmAtms (IsPre _)   atms@[IsPre _]           =  return atms
mrgAtmAtms p@(IsPre _) (d@(Disjoint _ _):atms)  =  fmap (d:) $ mrgAtmAtms p atms
mrgAtmAtms p@(IsPre _) (c@(Covers _ _)  :atms)  =  fmap (c:) $ mrgAtmAtms p atms
\end{code}

\subsubsection{Failure Case}
If none of the above arise, then we currently have a problem,
probably with \texttt{mrgAtmCond} above.
\begin{code}
mrgAtmAtms atm atms
 = fail $ unlines' [ "Unexpected fail in mrgAtmAtms:"
                   , "atm is "++show atm
                   , "atms are "++ show atms ]
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
scDischarge :: Monad m => SideCond -> SideCond -> m SideCond
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
scDischarge _ []    =  return scTrue  -- G => true   is  true
scDischarge [] scL  =  return scL     -- true => L is L,  i.e., not discharged
\end{code}
\begin{code}
scDischarge anteSC cnsqSC
  = scDischarge' (groupByGV anteSC) (groupByGV cnsqSC)
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
scDischarge' :: Monad m => [(GenVar,[AtmSideCond])] -> [(GenVar,[AtmSideCond])]
              -> m SideCond
scDischarge' _ []      =  return scTrue                   -- discharged
scDischarge' [] grpsL  =  return $ concat $ map snd grpsL -- not discharged
scDischarge' (grpG@(gvG,ascsG):restG) grpsL@(grpL@(gvL,ascsL):restL)
  | gvG < gvL  =  scDischarge' restG grpsL -- grpG not needed
  | gvG > gvL  =  do -- nothing available to discharge grpL
                     rest' <- scDischarge' restG restL
                     return (ascsL++rest')
  | otherwise  =  do -- use grpG to discharge grpL
                     ascs' <- grpDischarge (pdbg "ascsG" ascsG) $ pdbg "ascsL" ascsL
                     rest' <- scDischarge' restG restL
                     return (pdbg "ascs'" ascs'++rest')
\end{code}

\newpage

\textbf{As above, we only consider \texttt{Disjoint} and \texttt{Covers}
for now.}

The following code assumes that the \texttt{GenVar} component
is the same in all of the \texttt{AtmSideCond}.

Here again, we have the form
\begin{equation}
 \left( \bigwedge_{i \in \setof{D,C,pre}} G_i \right)
 \implies
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
grpDischarge :: Monad m => [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
grpDischarge _ []  =  return []
grpDischarge ascsG (ascL:ascsL)
  = do ascL'  <- ascsDischarge ascsG ascL
       ascsL' <- grpDischarge ascsG ascsL
       return (ascL'++ascsL')
\end{code}

Here we are trying to show
\begin{equation*}
 \left( \bigwedge_{i \in \setof{D,C,pre}} G_i \right)
 \implies
 L_j \quad \where \quad j \in \setof{D,C,pre}
\end{equation*}
\begin{code}
ascsDischarge :: Monad m => [AtmSideCond] -> AtmSideCond -> m [AtmSideCond]
ascsDischarge [] ascL = return [ascL]
ascsDischarge (ascG:ascsG) ascL
  =  case ascDischarge ascG ascL of
      Yes []       ->  return []
      Yes [ascL']  ->  ascsDischarge ascsG ascL'
      But msgs     ->  fail $ unlines msgs
\end{code}

\newpage

Finally, we get to where the real work is done.trying to show
Here we are trying to show:
\begin{equation*}
 G_i
 \implies
 L_j \quad \where \quad i,j \in \setof{D,C,pre}
\end{equation*}
\begin{code}
ascDischarge :: Monad m => AtmSideCond -> AtmSideCond -> m [AtmSideCond]
-- ascDischarge ascG ascL
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

\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & \mapsto & (D_L\setminus D_G) \disj V
\\ & \mapsto & \true, \quad \textbf{if } D_L \subseteq D_G
\end{eqnarray*}
\begin{code}
ascDischarge (Disjoint _ dG) (Disjoint gv dL)
  | dL `S.isSubsetOf` dG  =  return [] -- true
  | otherwise             =  return [Disjoint gv (dL S.\\ dG)]
\end{code}

\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & \mapsto & (C_G \cap D_L) \disj V
\\ & \mapsto & \true, \quad \IF~ C_G = \emptyset
\\ & \mapsto & \false, \quad \IF~ \emptyset \subset C_G \subseteq D_L
\end{eqnarray*}
\begin{code}
ascDischarge (Covers _ cG) (Disjoint gv dL)
  | S.null cG             =  return []
  | cG `S.isSubsetOf` dL  =  fail "ascDischarge: covers ==> not disjoint"
  | otherwise             =  return [Disjoint gv (cG `S.intersection` dL)]
\end{code}

\begin{eqnarray*}
   C_G \supseteq V \discharges C_L \supseteq V
   & \mapsto & (C_G \cap C_L) \supseteq V
\\ & \mapsto & \true, \quad \textbf{if } C_G \subseteq C_L
\end{eqnarray*}
\begin{code}
ascDischarge (Covers _ cG) (Covers gv cL)
  | cG `S.isSubsetOf` cL  =  return [] -- true
  | otherwise             =  return [Covers gv (cG `S.intersection` cL)]
\end{code}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & \mapsto & (C_L \setminus D_G) \supseteq V
\\ & \mapsto & \false, \quad \textbf{if } \emptyset \subset C_L \subseteq D_G
\end{eqnarray*}
\begin{code}
ascDischarge (Disjoint _ dG) c@(Covers gv cL)
  | S.null cL             =  return [c]
  | cL `S.isSubsetOf` dG  =  fail "ascDischarge: disjoint ==> not covers"
  | otherwise             =  return [Covers gv (cL S.\\ dG)]
\end{code}

Anything else is not handled right now;
\begin{code}
ascDischarge _ _ = fail "ascDischarge: NYfI"
\end{code}

\newpage
When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check if all the variables in that residual
are those that were unbound after initial matching.
If not, then the match application fails.
Otherwise, the goal side-condition is extended by this residual.
\begin{code}
checkUnboundInvolved :: Monad m => VarSet -> SideCond -> SideCond -> m SideCond
checkUnboundInvolved unbound scC []  =  return scC  -- no change
checkUnboundInvolved unbound scC scD
  | unbound `inAll` scD   =  scC `mrgSideCond` scD
  | otherwise  =  fail "checkUnboundInvolved: fails"
\end{code}

\begin{code}
inAll :: VarSet -> SideCond -> Bool
inAll unb = all (involvedIn unb)

involvedIn :: VarSet -> AtmSideCond -> Bool
involvedIn unb (Disjoint _ d) =  unb `overlaps` d
involvedIn unb (Covers _ c)   =  unb `overlaps` c
involvedIn _   _              =  False
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


\subsection{Assertions}

An assertion is simply a predicate term coupled with side-conditions.
\begin{code}
type Assertion = (Term, SideCond)
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
