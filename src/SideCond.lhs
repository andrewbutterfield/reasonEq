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
, SideCond, scTrue, isTrivialSC, onlyFreshSC
, mrgAtmCond, mrgSideCond, mkSideCond
, scDischarge
, isFloatingASC
, notin, covers, pre, fresh
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
given a logic like ours with explict expression and predicate
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
In some cases, we will use a list-variable to denoted a list of terms,
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
ascVSet _                =  Nothing
\end{code}

\newpage
\subsubsection{Checking Atomic Sideconditions}

It is possible to simplify some proposed atomic side-conditions
to either true or false.
Here we provide a monadic function that fails if the condition
is demonstrably false,
and otherwise returns a \texttt{Maybe} type,
where \texttt{Nothing} denotes a condition that is true.
\begin{code}
scCheck :: Monad m => AtmSideCond -> m (Maybe AtmSideCond)
\end{code}
Here, $z$ denotes an (standard) observation variable,
$T$ denotes a standard term variable,
and $g$ denotes either $z$ or $T$.

\paragraph{Checking Disjoint}

\begin{eqnarray*}
   \emptyset       \disj    g  && \true
\\ \dots,z,\dots   \disj    z  && \false
\\ \{stdObs\}\setminus z \disj z && \true
\end{eqnarray*}
Note that we cannot deduce (here) that $T \disj T$ is false,
because $T$ could correspond to the empty set.
Nor can we assume $T \disj z$ is false, because $T$ could contain $z$.
\begin{code}
scCheck asc@(Disjoint sv@(StdVar v) vs)
  | S.null vs         =  return Nothing
  | not $ isObsVar v  =  return $ Just asc
  | sv `S.member` vs  =  fail "atomic disjoint is False"
  | all isObsGVar vs  =  return Nothing
\end{code}

\paragraph{Checking Covers}

\begin{eqnarray*}
   \emptyset       \supseteq z  && \false
\\ \dots,g,\dots{} \supseteq g  && \true
\\ \{stdObs\}\setminus z \supseteq z && \false
\end{eqnarray*}
Here, as $T$ could be empty,
we cannot deduce that $\emptyset \supseteq T$ is false.
Similarly, $T \supseteq z$ could also be true.
\begin{code}
scCheck asc@(Covers sv@(StdVar v) vs)
  | sv `S.member` vs  =  return Nothing
  | not $ isObsVar v  =  return $ Just asc
  | S.null vs         =  fail "atomic covers is False (null)"
  | all isObsGVar vs  =  fail "atomic covers is False (all std)"
\end{code}

\paragraph{Checking Precondition}


\begin{eqnarray*}
   pre \supseteq g  && \false,  \textrm{ if $g$ is an \texttt{After} variable}
\\ pre \supseteq g  && \true,  \textrm{ if $g$ is a \texttt{Before} variable}
\end{eqnarray*}
\begin{code}
scCheck asc@(IsPre v@(StdVar (Vbl _ _ vw)))
  | vw == After   =  fail "atomic ispre is False"
  | vw == Before  =  return Nothing
\end{code}

For anything else, we just return the condition unchanged.
In particular, we cannot do anything with freshness at this point.
\begin{code}
scCheck asc = return $ Just asc
\end{code}



\newpage
\subsection{Full Side Conditions}

Freshness is a special case of disjoint:
\begin{itemize}
  \item It applies to the whole goal or law
  \item If the pattern fresh variables are bound in a match,
       then the corresponding candidate variable
        must satisfy the disjoint side-condition against
       the entire goal.
  \item If the pattern fresh variables are floating (not bound in a match)
   then we can generate new candidate variables that
   do satisfy the disjoint side-condition against
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
onlyFreshSC (ascs,fvs) = null ascs
\end{code}

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
mrgAtmCond :: Monad m => AtmSideCond -> [AtmSideCond] -> m [AtmSideCond]
\end{code}




1st ASC is easy:
\begin{code}
mrgAtmCond asc []
  = do masc <- scCheck asc
       case masc of
         Nothing ->  return [] -- asc is in fact true
         Just asc' -> return [asc']
\end{code}

Subsequent ones mean searching to see if there are already ASCs with the
same general-variable:
\begin{code}
mrgAtmCond asc ascs
  = do masc <- scCheck asc
       case masc of
         Nothing ->  return ascs
         Just asc' -> splice (mrgAtmAtms asc) $ brkspnBy (compareGV asc) ascs

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
If the general variable is required to be fresh,
then this is inconsistent with \texttt{Covers}.

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

\subsubsection{Merging Atomic Lists}

\begin{code}
mrgAtmCondLists :: Monad m => [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
mrgAtmCondLists ascs1 [] = return ascs1
mrgAtmCondLists ascs1 (asc:ascs2)
     = do ascs1' <- mrgAtmCond asc ascs1
          mrgAtmCondLists ascs1' ascs2
\end{code}

\subsubsection{Merging Atomic and Freshness Side-Conditions}


\begin{code}
mrgAtomicFreshConditions :: Monad m => VarSet -> [AtmSideCond] -> m SideCond
mrgAtomicFreshConditions freshvs ascs
  | freshvs `disjoint` coverVarsOf ascs  =  return (ascs,freshvs)
  | otherwise  =  fail "Fresh variables cannot cover terms."

coverVarsOf :: [AtmSideCond] -> VarSet
coverVarsOf ascs = S.unions $ map coversOf ascs
coversOf (Covers _ vs)  =  vs
coversOf _              =  S.empty
\end{code}

\subsection{From ASC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: Monad m => [AtmSideCond] -> VarSet -> m SideCond
mkSideCond ascs fvs
 = do ascs' <-  mrgAtmCondLists [] ascs
      mrgAtomicFreshConditions fvs ascs
\end{code}


\subsubsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each ASC and fresh set from the one into the other,
one at a time.
\begin{code}
mrgSideCond :: Monad m => SideCond -> SideCond -> m SideCond
mrgSideCond (ascs1,fvs1) (ascs2,fvs2)
     = do ascs' <- mrgAtmCondLists ascs1 ascs2
          mrgAtomicFreshConditions (fvs1 `S.union` fvs2) ascs'
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
 \vdash
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
scDischarge anteSC@(anteASC,anteFvs) cnsqSC@(cnsqASC,cnsqFvs)
  | isTrivialSC cnsqSC  =  return scTrue  -- G => true   is   true
  | isTrivialSC anteSC  =  return cnsqSC  -- true => L   is   L, not discharged
  | otherwise
     = do asc' <- scDischarge' (groupByGV anteASC) (groupByGV cnsqASC)
          let fvs' = cnsqFvs S.\\ anteFvs
          return (asc',fvs')
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
              -> m [AtmSideCond]
scDischarge' _ []      =  return []                   -- discharged
scDischarge' [] grpsL  =  return $ concat $ map snd grpsL -- not discharged
scDischarge' (grpG@(gvG,ascsG):restG) grpsL@(grpL@(gvL,ascsL):restL)
  | gvG < gvL  =  scDischarge' restG grpsL -- grpG not needed
  | gvG > gvL  =  do -- nothing available to discharge grpL
                     rest' <- scDischarge' restG restL
                     return (ascsL++rest')
  | otherwise  =  do -- use grpG to discharge grpL
                     ascs' <- grpDischarge ascsG ascsL
                     rest' <- scDischarge' restG restL
                     return (ascs'++rest')
\end{code}

\newpage

\textbf{As above, we only consider \texttt{Disjoint} and \texttt{Covers}
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
 \vdash
 L_j \quad \where \quad j \in \setof{D,C,pre}
\end{equation*}
\begin{code}
ascsDischarge :: Monad m => [AtmSideCond] -> AtmSideCond -> m [AtmSideCond]
ascsDischarge [] ascL = return [ascL]
ascsDischarge (ascG:ascsG) ascL
  =  case ascDischarge (pdbg "ascG" ascG) $ pdbg "ascL" ascL of
      Yes []       ->  return []
      Yes [ascL']  ->  ascsDischarge ascsG ascL'
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

One special case worth special treatment is a translated law side-condition
of the form $\emptyset \supseteq v$, where $v$ is a standard variable.
This is simply false.
\begin{code}
ascDischarge _ (Covers (StdVar (Vbl _ ObsV _)) dL)
  | S.null dL  =  fail ("Empty set cannot cover a standard obs. variable")
\end{code}

Otherwise, we work through the combinations:
\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true, \quad\IF\quad D_L \subseteq D_G
\\ & \mapsto & (D_L\setminus D_G) \disj V
\end{eqnarray*}
\begin{code}
ascDischarge (Disjoint _ dG) (Disjoint gv dL)
  | dL `S.isSubsetOf` dG  =  return [] -- true
  | otherwise             =  return [Disjoint gv (dL S.\\ dG)]
\end{code}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false,
     \quad\IF\quad C_L \subseteq D_G \land isStdObs(V)
\\ & \mapsto & (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
\begin{code}
ascDischarge (Disjoint _ dG) c@(Covers gv cL)
  | cL `S.isSubsetOf` dG && isObsGVar gv  =  fail "Disj=>emptyCover"
  | otherwise                             =  return [Covers gv (cL S.\\ dG)]
\end{code}

\begin{eqnarray*}
   C_G \supseteq V \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad C_G \subseteq C_L
\\ & = & \false, \quad \IF \quad C_G \disj C_L \land isStdObs(V)
\\ & \mapsto & (C_G \cap C_L) \supseteq V
\end{eqnarray*}
\begin{code}
ascDischarge (Covers _ cG) (Covers gv cL)
  | cG `S.isSubsetOf` cL  =  return []
  | cG `disjoint` cL && isObsGVar gv  =  fail "CoverDisj=>noCover"
  | otherwise  =  return [Covers gv (cG `S.intersection` cL)]
\end{code}


\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & = & \true, \quad \IF~ C_G\cap D_L = \emptyset
\\ & \mapsto & D_L \disj V
\end{eqnarray*}
\begin{code}
ascDischarge (Covers _ cG) d@(Disjoint gv dL)
  | S.null (cG `S.intersection` dL)  =  return []
  | otherwise                        =  return [d]
\end{code}


Anything else is not handled right now;
\begin{code}
ascDischarge _ ascL = return [ascL]
\end{code}

\newpage
When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check that \emph{all} the atomic side-conditions in that residual
mention variables that are marked as ``floating''.
Only these can possibly be instantiated to satisfy the residual side-condition.
\begin{code}
isFloatingASC :: AtmSideCond -> Bool
isFloatingASC = isFloatingGVar . ascGVar
\end{code}
One exception to this, during law matching,
is that coverage may reduce to the empty set
because unbound variables given a temporary binding
to a ``?'' variable (\texttt{instantiateFloating})
will not cancel out other variables that they should be able to do,
if instantiated properly.
\begin{code}
tolerateAutoOrNull :: VarSet -> AtmSideCond -> Bool
tolerateAutoOrNull unbound (Disjoint _ d) =  unbound `overlaps` d
tolerateAutoOrNull unbound (Covers _ c)   =  S.null c || unbound `overlaps` c
tolerateAutoOrNull _       _              =  False
autoOrNullInAll unbound = all (tolerateAutoOrNull unbound)
\end{code}



\newpage
\subsection{Building side-conditions.}

Simple side-condition builders.

$\lst v \disj \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  ([ Disjoint tV (S.fromList vl) ], S.empty)
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  ([ Covers tV (S.fromList vl) ], S.empty)
\end{code}

$pre \supseteq \fv(T)$
\begin{code}
pre :: GenVar -> SideCond
pre tV  = ([ IsPre tV ], S.empty)
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
     , tst_scChkCovers
     , tst_scChkIsPre ]


tstFalse = Nothing
tstTrue  = Just Nothing
tstWhatever sc = Just $ Just sc

tst_scChkDisjoint
 = testGroup "Disjoint"
    [ testCase "gv_a `disjoint` empty is True"
       ( scCheck (Disjoint gv_a S.empty) @?= tstTrue )
    , testCase "v_e `disjoint` empty is True"
       ( scCheck (Disjoint v_e S.empty) @?= tstTrue )
    , testCase "gv_a `disjoint` {gv_a} is False"
       ( scCheck (Disjoint gv_a $ S.singleton gv_a) @?= tstFalse )
    , testCase "gv_a `disjoint` {gv_b} is True"
       ( scCheck (Disjoint gv_a $ S.singleton gv_b) @?= tstTrue )
    , testCase "v_e `disjoint` {v_e} stands"
       ( scCheck (Disjoint v_e $ S.singleton v_e)
         @?= tstWhatever  (Disjoint v_e $ S.singleton v_e) )
    , testCase "v_e `disjoint` {v_f} stands"
       ( scCheck (Disjoint v_e $ S.singleton v_f)
         @?= tstWhatever  (Disjoint v_e $ S.singleton v_f) )
    , testCase "v_e `disjoint` {gv_a} stands"
       ( scCheck (Disjoint v_e $ S.singleton gv_a)
         @?= tstWhatever  (Disjoint v_e $ S.singleton gv_a) )
    , testCase "gv_a `disjoint` {v_f} stands"
       ( scCheck (Disjoint gv_a $ S.singleton v_f)
         @?= tstWhatever  (Disjoint gv_a $ S.singleton v_f) )
    , testCase "gv_a `disjoint` {gv_b,v_f} stands"
       ( scCheck (Disjoint gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (Disjoint gv_a $ S.fromList [gv_b,v_f]) )
    ]

tst_scChkCovers
 = testGroup "Covers"
    [ testCase "gv_a `coveredby` empty is False"
       ( scCheck (Covers gv_a S.empty) @?= tstFalse )
    , testCase "v_e `coveredby` empty stands"
       ( scCheck (Covers v_e S.empty)
         @?= tstWhatever (Covers v_e S.empty) )
    , testCase "gv_a `coveredby` {gv_a} is True"
       ( scCheck (Covers gv_a $ S.singleton gv_a) @?= tstTrue )
    , testCase "gv_a `coveredby` {gv_b} is False"
       ( scCheck (Covers gv_a $ S.singleton gv_b) @?= tstFalse )
    , testCase "v_e `coveredby` {v_e} is True"
       ( scCheck (Covers v_e $ S.singleton v_e) @?= tstTrue )
    , testCase "v_e `coveredby` {v_f} stands"
       ( scCheck (Covers v_e $ S.singleton v_f)
         @?= tstWhatever  (Covers v_e $ S.singleton v_f) )
    , testCase "v_e `coveredby` {gv_a} stands"
       ( scCheck (Covers v_e $ S.singleton gv_a)
         @?= tstWhatever  (Covers v_e $ S.singleton gv_a) )
    , testCase "gv_a `coveredby` {v_f} stands"
       ( scCheck (Covers gv_a $ S.singleton v_f)
         @?= tstWhatever  (Covers gv_a $ S.singleton v_f) )
    , testCase "gv_a `coveredby` {gv_b,v_f} stands"
       ( scCheck (Covers gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (Covers gv_a $ S.fromList [gv_b,v_f]) )
    ]

tst_scChkIsPre
 = testGroup "IsPre"
    [ testCase "is-pre(gv_a) is True"
       ( scCheck (IsPre gv_a) @?= tstTrue )
    , testCase "is-pre(gv_a') is False"
       ( scCheck (IsPre gv_a') @?= tstFalse )
    , testCase "is-pre(v_e) is True"
       ( scCheck (IsPre v_e) @?= tstTrue )
    , testCase "is-pre(v_e') is False"
       ( scCheck (IsPre v_e') @?= tstFalse )
    , testCase "is-pre(gv_s) stands"
       ( scCheck (IsPre gv_s) @?= tstWhatever (IsPre gv_s) )
    ]
\end{code}

\subsubsection{Merging Tests}

\begin{code}
tst_mrgAtmCond :: TF.Test
tst_mrgAtmCond
 = testGroup "Merging Side-Conditions"
     [ testCase "merge gv_a `disjoint` empty  into [] is True"
        ( mrgAtmCond (Disjoint gv_a S.empty) [] @?= Just [] )
     , testCase "merge gv_a `disjoint` {gv_a} into [] is False"
        ( mrgAtmCond (Disjoint gv_a $ S.singleton gv_a) [] @?= Nothing )
     , testCase "merge v_e `coveredby` {v_f}  into [] is [itself]"
        ( mrgAtmCond (Covers v_e $ S.singleton v_f) []
          @?= Just [Covers v_e $ S.singleton v_f] )
     , testCase "merge gv_a `disjoint` empty  into [asc(gv_b)] is [asc(gv_b)]]"
        ( mrgAtmCond (Disjoint gv_a S.empty) [asc1] @?= Just [asc1] )
     , testCase "merge gv_a `disjoint` {gv_a} into [asc(gv_b)] is False"
        ( mrgAtmCond (Disjoint gv_a $ S.singleton gv_a) [asc1] @?= Nothing )
     , testCase
        "merge v_e `coveredby` {v_f}  into [asc(gv_b)] is [asc(gv_b),itself]"
        ( mrgAtmCond (Covers v_e $ S.singleton v_f) [asc1]
          @?= Just [asc1,Covers v_e $ S.singleton v_f] )
     ]

asc1 = (Covers gv_b $ S.fromList [gv_b,v_f])
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
  = testGroup "Disjoint discharges ..."
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
