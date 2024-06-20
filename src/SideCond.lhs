\chapter{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  Uniformity, pattern Unif, pattern NonU
, usame, usamel, usameg
, setWhen, lsetWhen, gsetWhen
, AtmSideCond
, pattern Disjoint, pattern CoveredBy
, setASCUniformity
, ascGVar, ascVSet
, SideCond, scTrue, isTrivialSC
, onlyFreshSC, onlyInvolving, onlyFreshOrInvolved
, scGVars, scVarSet
, mrgAtmCond, mrgSideCond, mrgSideConds, mkSideCond
, scDischarge
, isFloatingASC
, notin, covers, fresh
, findGenVar, findAllGenVar, findCoveredGenVar
-- , citingASCs   -- not used anywhere!
, (.:), mrgscs
, int_tst_SideCond
) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import YesBut
import Utilities
import LexBase
import Variables
import AST

import Test.HUnit hiding (Assertion)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}


\newpage
\section{Introduction}

A side-condition is a property used in laws,
typically putting a constraint on the free variables of some term.
In many logics, these can be checked by simple inspection of a term.
However,
given a logic like ours with explicit expression and predicate
(a.k.a. \emph{schematic}) variables this is not always possible.

A side condition is about a relationship between the free variables
of term ($T$),
and a set of other (general) variables ($x,\lst{v}$).
In general we have a conjunction of atomic conditions,
but we need to be able to distinguish between no conditions (always ``true'')
and inconsistent conditions
(e.g. $x \disj \fv(T) \land x = \fv(T) $, always ``false'').
As a false side-condition means a match failure,
we do not represent them explicitly.
Instead, any operation on side-conditions that could result
in an inconsistent result should fail, gracefully.

\subsection{Atomic Side-Conditions}

An atomic side-condition (ASC) can have one of the following forms,
where $T$ abbreviates $\fv(T)$:
\begin{eqnarray*}
   x,\lst v   \disj  T
   && \mbox{disjoint, short for }\{x,\lst v\} \cap \fv(T) = \emptyset
\\ x,\lst v \supseteq T 
   && \mbox{covering, short for }\{x,\lst v\} \supseteq \fv(T)
\\ x_d,\lst v_d \supseteq_d T 
   && \mbox{dynamic coverage, short for } \{x_d,\lst v_d\} \supseteq \dfv(T)
\\ pre      \supseteq T && \mbox{pre-condition, no dashed variables}
\end{eqnarray*}
For dynamic coverage, a fuller more rigorous definition is:
\begin{equation*}
V \supseteq_d T 
\quad\defs\quad 
(\forall g \in V \bullet \isdyn(g))
\land
V \supseteq \dfv(T)
\end{equation*}

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
\\ \emptyset \supseteq z   && \false
\\ \emptyset \supseteq_d z && \lnot\isdyn(z)
\\ pre       \supseteq z   && z \textrm{ is a \texttt{Before} variable}
\end{eqnarray*}
For list variables, we can add:
\begin{eqnarray*}
   \lst\ell  \supseteq \lst\ell\less x,\dots  && \true
\\ \lst\ell  \supseteq_d \lst\ell\less x,\dots  && \isdyn(\lst\ell)
\end{eqnarray*}


We also need to take account of known variables of various kinds
when evaluating and building side-conditions.

\newpage
\subsection{Side-Condition Temporality}

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
We need to add an easy check that two dynamic
variables differ only in their temporality.
\begin{code}
usame :: Variable -> Variable -> Bool
usame (Vbl i1 vc1 vw1) (Vbl i2 vc2 vw2)
       =  i1==i2 && vc1==vc2 && isDynamic vw1 && isDynamic vw2
usamel :: ListVar -> ListVar -> Bool
usamel (LVbl v1 is1 js1) (LVbl v2 is2 js2)
        = v1 `usame` v2 && is1==is2 && js1==js2
usameg :: GenVar -> GenVar -> Bool
usameg (StdVar v1) (StdVar v2) = v1 `usame` v2
usameg (LstVar lv1) (LstVar lv2) = lv1 `usamel` lv2
\end{code}
It also helps to change the dynamic temporality of a variable.

\begin{code}
setWhen :: VarWhen -> Variable -> Variable
setWhen vw (Vbl i vc _)  = Vbl i vc vw
lsetWhen :: VarWhen -> ListVar -> ListVar
lsetWhen vw (LVbl (Vbl i vc _) is js)  = LVbl (Vbl i vc vw) is js
gsetWhen :: VarWhen -> GenVar -> GenVar
gsetWhen vw (StdVar v)   = StdVar $ setWhen  vw v
gsetWhen vw (LstVar lv)  = LstVar $ lsetWhen vw lv
\end{code}
These should only be applied to variables known to be dynamic.


\section{Atomic Side-Conditions}

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

Selectors:
\begin{code}
ascUnfm :: AtmSideCond -> Uniformity
ascUnfm (Disjoint  u _ _)  =  u
ascUnfm (CoveredBy u _ _)  =  u

isUniform :: AtmSideCond -> Bool
isUniform asc  =  ascUnfm asc == Unif

ascGVar :: AtmSideCond -> GenVar
ascGVar (Disjoint  _ gv _)  =  gv
ascGVar (CoveredBy _ gv _)  =  gv

ascVSet :: AtmSideCond -> VarSet
ascVSet (Disjoint  _ _ vs)  =  vs
ascVSet (CoveredBy _ _ vs)  =  vs
\end{code}
This last function is less useful because it loses uniformity information
needed to interpret dynamic variables property
(used below and in \texttt{Instantiate.lhs}).

We can determine if the components
used to make an atomic side-condition are ``uniform''.
A relation $~\Re~$ between a general variable $g^t$ of temporality $t$
and a set of general variables $G^\tau$ with temporality drawn from $\tau$,
is uniform if:
\begin{itemize}
  \item The general variable $g^t$ is dynamic
  \item All the variables in $G^\tau$ are dynamic
  \item All of $\setof g^t \cup G^\tau$ have the same dynamicity
     (i.e., $\tau = \setof t$).
\end{itemize}
\begin{code}
areUniform :: GenVar -> VarSet -> Bool
areUniform gv vs
  = S.size whens == 1 && isDynamic (head $ S.elems whens)
  where
    whens = S.map gvarWhen (S.insert gv vs)
\end{code}
If $g^t ~\Re~ G^\tau$ is uniform,
we interpret it as specifiying the following:
$$
  g ~\Re~ G
  \land
  g' ~\Re~ G'
  \land
  g_i ~\Re~ G_s, \mbox{ for all subscript } s \mbox{ in use.}
$$
We \emph{represent} the above using the \texttt{Before} form: $g ~\Re~ G$.

\subsection{Checking Atomic Sideconditions}

We need to ensure that the \texttt{Uniformity} component
of an atomic side-condition is set correctly.
\begin{code}
setASCUniformity :: AtmSideCond -> AtmSideCond
setASCUniformity (Disjoint  _ gv vs)
  | areUniform gv vs  =  Disjoint Unif (dnGVar gv) (S.map dnGVar vs)
  | otherwise         =  Disjoint NonU         gv                vs
setASCUniformity (CoveredBy _ gv vs)
  | areUniform gv vs  =  CoveredBy Unif (dnGVar gv) (S.map dnGVar vs)
  | otherwise         =  CoveredBy NonU         gv                vs
\end{code}

We provide some builders that set uniformity:
\begin{code}
disjwith :: GenVar -> VarSet -> AtmSideCond
gv `disjwith` vs  =  setASCUniformity $ Disjoint NU gv vs

coveredby :: GenVar -> VarSet -> AtmSideCond
gv `coveredby` vs  =  setASCUniformity $ CoveredBy NU gv vs
\end{code}

It is also possible to simplify some proposed atomic side-conditions
to either true or false.
An important shortcut condition is when we have a dynamic general variable
along with a variable set, all of whose members are dynamic.
Both disjointness and coverage can be simplified
if the general variable's temporality
does not match that of any of the set variables.
\begin{code}
isTempDisjointASC :: GenVar -> VarSet -> Bool
isTempDisjointASC gv vs
  = isDynamic gvWhen && tempdisjoint
  where
    gvWhen        =  gvarWhen gv
    vsWhens       =  S.map gvarWhen vs
    tempdisjoint  =  not (gvWhen `S.member` vsWhens)
\end{code}

\newpage
Here we provide a monadic function that fails if the condition
is demonstrably false,
and otherwise returns a \texttt{Maybe} type,
where \texttt{Nothing} denotes a condition that is true.

We need to do this in general
in the context of what is ``known'' about variables.
\begin{code}
mscTrue = Nothing
ascCheck :: MonadFail m => [Subscript] -> AtmSideCond -> m (Maybe AtmSideCond)
\end{code}
Here, $z$ denotes an (standard) observation variable,
$T$ denotes a standard term variable,
and $g$ denotes either $z$ or $T$.
We also use the case conventions described earlier ($P, p, p'$).


\subsubsection%
{Checking Disjoint $ V \disj g$}

\begin{eqnarray*}
   \emptyset             \disj g           &&   \true
\\ \dots,z,\dots         \disj z           &&   \false
\\ \{stdObs\}\setminus z \disj z           &&   \true
\\ V,g\textrm{ are temporally disjoint}    &&   \true
\end{eqnarray*}

Note that we cannot deduce (here) that $T \disj T$ is false,
because $T$ could correspond to the empty set.
Nor can we assume $T \disj z$ is false, because $T$ could contain $z$.
\begin{code}
ascCheck ss asc@(Disjoint _ gv vs)
  | S.null vs                 =  return mscTrue
  | isTempDisjointASC gv vs   =  return mscTrue
  | not $ isObsGVar gv        =  return $ Just $ setASCUniformity asc
  -- gv is an observation variable below here....
  | gv `S.member` vs          =  report "atomic Disjoint is False"
  | all isStdV    vs          =  return mscTrue
  where
    showsv = "gv = "++show gv
    showvs = "vs = "++show vs
    report msg = fail $ unlines' [msg,showsv,showvs]
\end{code}

\subsubsection{Checking CoveredBy $V \supseteq g$}

\begin{eqnarray*}
   \emptyset             \supseteq z           && \false
\\ \dots,g,\dots{}       \supseteq g           && \true
\\ \{stdObs\}\setminus z \supseteq z           && \false
\\ \ell\setminus Z \supseteq \ell\setminus (Z\cup W) 
     && \true
\\ V,g\textrm{ are temporally disjoint}        && \false
\end{eqnarray*}

Here, as $T$ could be empty,
we cannot deduce that $\emptyset \supseteq T$ is false.
Similarly, $T \supseteq z$ could also be true.
\begin{code}
ascCheck ss asc@(CoveredBy _ gv vs)
  -- | gv `S.member` vs  =  return mscTrue -- subsumed by next line
  | any (gvCovBy gv) vs  =  return mscTrue
  | isdisj               =  report "non-U atomic covers is False (disjoint)"
  | not $ isObsGVar gv   =  return $ Just $ setASCUniformity asc
  -- gv is an observation variable not in vs below here....
  | S.null vs            =  report "atomic covers is False (null)"
  | all isStdV vs        =  report "atomic covers is False (all std)"
  where 
    isdisj = isTempDisjointASC gv vs
    showsv = "gv = "++show gv
    showvs = "vs = "++show vs
    report msg = fail $ unlines' [msg,showsv,showvs]
\end{code}

In all other cases, we return the atomic condition with uniformity set:
\begin{code}
ascCheck _ asc = return $ Just $ setASCUniformity asc
\end{code}

Is $\ell\less V$ covered by $\kappa\less W$ ?
It is if $\ell=\kappa$ and $W \subseteq V$.
\begin{code}
gvCovBy :: GenVar -> GenVar -> Bool
gvCovBy (LstVar (LVbl v is js)) (LstVar (LVbl covv isv jsv))
  = v == covv && isv `issubset` is && jsv `issubset` js
gvCovBy _ _ = False
\end{code}


\newpage
\section{Full Side Conditions}

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
onlyFreshSC (ascs,_) = null ascs
\end{code}
or involve variables in a designated set:
\begin{code}
onlyInvolving :: VarSet -> SideCond -> Bool
onlyInvolving involved (ascs,_) = all (onlyWith involved) ascs

onlyWith :: VarSet -> AtmSideCond -> Bool
onlyWith involved (SD _ gv vs)
  = gv `S.member` involved || involved `overlaps` vs
onlyWith involved (SS _ gv vs)
  = gv `S.member` involved || involved `overlaps` vs
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
This latter function is less useful because it loses uniformity information
needed to interpret dynamic variables property
(used in \texttt{Assertions.lhs}).

\section{Merging Side-Conditions}

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
mrgAtmCond :: MonadFail m => [Subscript]
           -> AtmSideCond -> [AtmSideCond] -> m [AtmSideCond]
\end{code}

1st ASC is easy:
\begin{code}
mrgAtmCond ss asc []
  = do masc <- ascCheck ss asc
       case masc of
         Nothing ->  return [] -- asc is in fact true
         Just asc' -> return [asc']
\end{code}

Subsequent ones mean searching to see if there are already ASCs with the
same general-variable:
\begin{code}
mrgAtmCond ss asc ascs
  = do masc <- ascCheck ss asc
       case masc of
         Nothing ->  return ascs
         Just asc' -> splice (mrgAtmAtms ss asc) $ brkspnBy (compareGV asc) ascs

compareGV asc1 asc2  =  ascGVar asc1 `compare` ascGVar asc2
sameGV asc1 asc2     =  asc1 `compareGV` asc2 == EQ
\end{code}

\subsection{Merging one ASC with relevant others}

Now, merging an ASC in with other ASCs referring to the same general variable:
\begin{code}
mrgAtmAtms :: MonadFail m => [Subscript]
           -> AtmSideCond -> [AtmSideCond] -> m [AtmSideCond]
mrgAtmAtms ss asc [] = return [asc] -- it's the first.
\end{code}

Given one or more pre-existing ASCs for this g.v., we note the following possible
patterns:
\begin{verbatim}
[Disjoint]  [Disjoint,CoveredBy] [CoveredBy]
\end{verbatim}
If the general variable is required to be fresh,
then this is inconsistent with \texttt{CoveredBy}.

\subsection{ASC Merge Laws}

We have the following interactions,
where $D$ and $C$ are the variable-sets found
in \texttt{Disjoint} and \texttt{CoveredBy} respectively.
So the semantics of the disjoint ($D$) and covering ($C$) variable-sets,
parameterised by a general variable $G$,
are:
\begin{eqnarray*}
  \sem{\_}_{\_} &:& \power V \fun V \fun \Bool
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
\\ &=& \fv.G = \emptyset, \quad \IF \quad C\setminus D = \emptyset
\end{eqnarray*}
We note that an apparent contradiction between $D$ and $C$ (when $D \supseteq C$)
becomes an assertion that $G$ is closed.
For any given general variable $G$,
these laws ensure that we can arrange matters so that $D$ and $C$ are disjoint.

All the set operations used above preserve uniformity if both set arguments
are uniform.

It is worth noting Side conditions currently in use:
\begin{description}
  \item[Forall/Exists] (all non-uniform)\\
     $\lst x \disj P \qquad \lst x \disj e \qquad \lst y \disj P$
   \item[UClose] (all non-uniform)\\
    $\lst x \supseteq P \qquad \emptyset \supseteq P$
  \item[UTPBase]~\\
    $
      \lst O,\lst O' \supseteq P
      \quad
      \lst O,\lst O' \supseteq Q
      \quad
      \lst O,\lst O' \supseteq R
    $ \qquad (non-uniform)\\
    $
      \lst O \supseteq b
      \quad
      \lst O \supseteq e
      \quad
      \lst O \supseteq f
      \quad
      \lst O \supseteq x
      \qquad \textrm{(uniform)}
      \qquad
      O_0 \textrm{ fresh}
     $
\end{description}
Summary: All uses of disjointness are non-uniform.
All uniform specifications are coverings for expressions and variables.
Not seeing any mixing of these (yet!)

The key principles to combining conditions of possibly different uniformity are:
\begin{itemize}
  \item Let $S$ denote all the explicit subscripts in the non-uniform sides.
  \item Lift any uniform side with $x$ mapping to $x,x',x_i$ for all $ i \in S$.
  \item Perform the relevant set operation.
  \item If the result looks like a image of a lifting:
    then un-lift and mark as uniform;
  \item
    Otherwise:
     mark as non-uniform,
     \emph{
       but this requires us to replace a single uniform condition
       by several, one for each temporality,
       and hence each with a \textbf{different} general variable.
       This is not a good fit with the code architecture in use here.
     }
\end{itemize}

For now, we only handle simple cases,
those where both components have the same uniformity.
\subsection{Merging \texttt{Disjoint} into ASC}
\begin{code}
mrgAtmAtms ss (Disjoint u1 gv d0) [Disjoint u2 _ d1]
  | u1 == u2  =  return [Disjoint u1  gv (d0 `S.union` d1)]

mrgAtmAtms ss (Disjoint u1 gv d) [CoveredBy u2  _ c]
  | u1 == u2
    = if c `S.isSubsetOf` d
      then  return [CoveredBy u2 gv S.empty]
      else  return [Disjoint u1 gv d,CoveredBy u2 gv (c S.\\ d)]

mrgAtmAtms ss (Disjoint u1 gv d0) [Disjoint u2 _ d1,CoveredBy u3 _ c]
  | u1 == u2 && u1 == u3
    = if c `S.isSubsetOf` d'
      then  return [CoveredBy u3 gv S.empty]
      else  return [Disjoint u1 gv d',CoveredBy u3 gv (c S.\\ d')]
  where d' = d0 `S.union` d1
\end{code}


\subsection{Merging \texttt{CoveredBy} into ASC}
\begin{code}
mrgAtmAtms ss cov@(CoveredBy _ _ _) [dsj@(Disjoint _ _ _)]
                                                     =  mrgAtmAtms ss dsj [cov]

mrgAtmAtms ss (CoveredBy u1 gv c0) [CoveredBy u2 _ c1]
  | u1 == u2  = return [CoveredBy u1 gv (c0 `S.intersection` c1)]

mrgAtmAtms ss (CoveredBy u1 gv c0) [Disjoint u2 _ d,CoveredBy u3 _ c1]
  | u1 == u2 && u1 == u3
    = if c' `S.isSubsetOf` d
      then  return [CoveredBy u1 gv S.empty]
      else  return [Disjoint u2 gv d,CoveredBy u3 gv (c' S.\\ d)]
  where c' = c0 `S.union` c1
\end{code}

\subsection{Failure Case}
If none of the above arise, then we will need to consider how to
extend the above code to handle more cases.
\begin{code}
mrgAtmAtms ss atm atms
  = fail $ unlines' [ "Incompleteness in mrgAtmAtms:"
                    , "atm is   "++ show atm
                    , "atms are "++ show atms
                    , "ss is   "++ show ss ]
\end{code}

\subsection{Merging Atomic Lists}

\begin{code}
mrgAtmCondLists :: MonadFail m => [Subscript]
                -> [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
mrgAtmCondLists ss ascs1 [] = return ascs1
mrgAtmCondLists ss ascs1 (asc:ascs2)
     = do ascs1' <- mrgAtmCond ss asc ascs1
          mrgAtmCondLists ss ascs1' ascs2
\end{code}

\subsection{Merging Atomic and Freshness Side-Conditions}


\begin{code}
mrgAtomicFreshConditions :: MonadFail m => [Subscript]
                         -> VarSet -> [AtmSideCond] -> m SideCond
mrgAtomicFreshConditions ss freshvs ascs
  | freshvs `disjoint` coverVarsOf ss ascs  =  return (ascs,freshvs)
  -- the above might not work - `disjoint` may need more information
  | otherwise  =  fail "Fresh variables cannot cover terms."

coverVarsOf :: [Subscript] -> [AtmSideCond] -> VarSet
coverVarsOf ss ascs = S.unions $ map coversOf ascs
coversOf (CoveredBy NU  _ vs)  =  vs
coversOf _              =  S.empty
\end{code}

\section{From ASC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: MonadFail m => [Subscript] -> [AtmSideCond] -> VarSet -> m SideCond
mkSideCond ss ascs fvs
 = do ascs' <-  mrgAtmCondLists ss [] ascs
      mrgAtomicFreshConditions ss fvs ascs'
\end{code}


\subsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each ASC and fresh set from the one into the other,
one at a time.
\begin{code}
mrgSideCond :: MonadFail m => [Subscript] -> SideCond -> SideCond -> m SideCond
mrgSideCond ss (ascs1,fvs1) (ascs2,fvs2)
     = do ascs' <- mrgAtmCondLists ss ascs1 ascs2
          mrgAtomicFreshConditions ss (fvs1 `S.union` fvs2) ascs'
          -- the above may require a ss-savvy union?

mrgSideConds :: MonadFail m => [Subscript] -> [SideCond] -> m SideCond
mrgSideConds ss [] = return ([],S.empty)
mrgSideConds ss (sc:scs)
  = do  scs' <- mrgSideConds ss scs
        mrgSideCond ss sc scs'

\end{code}

\subsection{Side-Condition Operators}

We want some shorthands for assembling side-conditions,
that are also ``total'',
in that they return \texttt{SideCond} rather than \texttt{m SideCond}.
\begin{code}
(.:) :: SideCond -> SideCond -> SideCond
sc1 .: sc2 = fromJust $ mrgSideCond [] sc1 sc2
mrgscs :: [SideCond] -> SideCond
mrgscs = fromJust . mrgSideConds []
\end{code}
\textbf{
These are unsafe and should only be used for the definition of 
builtins or tests.
}


\newpage
\section{Discharging Side-conditions}

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
scDischarge :: MonadFail m => [Subscript] -> SideCond -> SideCond -> m SideCond
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
scDischarge ss anteSC@(anteASC,anteFvs) cnsqSC@(cnsqASC,cnsqFvs)
  | isTrivialSC cnsqSC  =  return scTrue  -- G => true   is   true
  | isTrivialSC anteSC  =  return cnsqSC  -- true => L   is   L, not discharged
  | otherwise
     = do asc' <- scDischarge' ss (groupByGV anteASC) (groupByGV cnsqASC)
          freshDischarge ss anteFvs cnsqFvs asc'
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

\subsection{Atomic Condition  Discharge}

Now onto processing those groups:
\begin{code}
scDischarge'  :: MonadFail m => [Subscript]
              -> [(GenVar,[AtmSideCond])] -> [(GenVar,[AtmSideCond])]
              -> m [AtmSideCond]
scDischarge' _ _ []      =  return []                   -- discharged
scDischarge' _ [] grpsL  =  return $ concat $ map snd grpsL -- not discharged
scDischarge' ss (grpG@(gvG,ascsG):restG) grpsL@(grpL@(gvL,ascsL):restL)
  | gvG < gvL  =  scDischarge' ss restG grpsL -- grpG not needed
  | gvG > gvL  =  do -- nothing available to discharge grpL
                     rest' <- scDischarge' ss restG restL
                     return (ascsL++rest')
  | otherwise  =  do -- use grpG to discharge grpL
                     ascs' <- grpDischarge ss ascsG ascsL
                     rest' <- scDischarge' ss restG restL
                     return (ascs'++rest')
\end{code}

\newpage

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
is to simplify an instance of (\ref{eqn:SideCond:discharge-form}).
However, we are assuming all the $G_i$ are true,
and want to know if that is enough to ensure that all the $L_j$
are also true.
There is an asymmetry here, which means that we should
use all the $G_i$ to try and discharge each $L_i$,
rather than the other way around.
\begin{code}
grpDischarge :: MonadFail m => [Subscript]
             -> [AtmSideCond] -> [AtmSideCond] -> m [AtmSideCond]
grpDischarge _ _ []  =  return []
grpDischarge ss ascsG (ascL:ascsL)
  = do ascL'  <- ascsDischarge ss ascsG ascL
       ascsL' <- grpDischarge ss ascsG ascsL
       return (ascL'++ascsL')
\end{code}

Here we are trying to show
\begin{equation*}
 \left( \bigwedge_{i \in \setof{D,C,pre}} G_i \right)
 \vdash
 L_j \quad \where \quad j \in \setof{D,C,pre}
\end{equation*}
\begin{code}
ascsDischarge :: MonadFail m => [Subscript]
              -> [AtmSideCond] -> AtmSideCond -> m [AtmSideCond]
ascsDischarge _ [] ascL = return [ascL]
ascsDischarge ss (ascG:ascsG) ascL
  =  case ascDischarge ss ascG ascL of
      Yes []       ->  return []
      Yes [ascL']  ->  ascsDischarge ss ascsG ascL'
      But msgs     ->  fail $ unlines msgs
\end{code}

\newpage

Finally, we get to where the real work is done.
Here we are trying to show:
\begin{equation*}
 G_i
 \vdash
 L_j \quad \where \quad i,j \in \setof{D,C}
\end{equation*}
\begin{code}
ascDischarge :: MonadFail m => [Subscript]
            -> AtmSideCond -> AtmSideCond -> m [AtmSideCond]
-- ascDischarge ss ascG ascL
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

A translated law side-condition of the form $\emptyset \supseteq v$,
where $v$ is a standard variable.
This is simply false.
\begin{code}
ascDischarge _ _ (CoveredBy _ (StdVar (Vbl _ ObsV _)) dL)
  | S.null dL  =  fail ("Empty set cannot cover a standard obs. variable")
\end{code}

Any occurrences of a floating variable in a translated law side-condition
should be retained.
We let $D_{?L}$ and $C_{?L}$ denote
the floating subsets of $D_L$ and $C_L$ respectively.

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

We also need to handle the uniformity markings properly here.

Now, we work through the combinations:
\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true, \quad\IF\quad D_L \subseteq D_G
\\ & \mapsto & (D_L\setminus D_G) \disj V
\end{eqnarray*}
\begin{code}
ascDischarge ss (Disjoint u1 _ dG) (Disjoint u2 gv dL)
  | linL `subset` linG  =  return [] -- true
  | otherwise           =  return [gv `disjwith` (linL `diff` linG)]
  where
    linG = (u1,lineariseVarSet dG)
    linL = (u2,lineariseVarSet dL)
    subset = isSCsubset ss
    diff s t = packUG $ doSCdiff ss s t
\end{code}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false,
     \quad\IF\quad C_L \subseteq D_G \land isStdObs(V)
\\ & \mapsto & (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
\begin{code}
ascDischarge ss (Disjoint u1 _ dG) c@(CoveredBy u2 gv cL)
  | linL `subset` linG
    && isObsGVar gv     =  fail "Disj=>emptyCover"
  | otherwise           =  return [gv `coveredby` (linL `diff` linG)]
  where
    linG = (u1,lineariseVarSet dG)
    linL = (u2,lineariseVarSet cL)
    subset = isSCsubset ss
    diff s t = packUG $ doSCdiff ss s t
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
ascDischarge ss (CoveredBy u1 _ cG) (CoveredBy u2 gv cL)
  | linG `subset` linL                =  return []
  | linG `disj` linL && isObsGVar gv  =  fail "CoverDisj=>noCover"
  | otherwise  =  return
                    [gv `coveredby` ((linG `intsct` linL) `union` linF)]
  where
    subset = isSCsubset ss
    disj = isSCdisjoint ss
    intsct = doSCint ss
    union s t = packUG $ doSCunion ss s t
    linG = (u1,lineariseVarSet cG)
    linL = (u2,lineariseVarSet cL)
    linF = (u2,lineariseVarSet $ S.filter isFloatingGVar cL)
\end{code}


\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & = & \true, \quad \IF~ C_G\cap D_L = \emptyset
\\ & \mapsto & D_L \disj V
\end{eqnarray*}
\begin{code}
ascDischarge ss (CoveredBy u1  _ cG) d@(Disjoint u2  gv dL)
  | linG `disj` linL  =  return []
  | otherwise         =  return [d]
  where
    disj = isSCdisjoint ss
    linG = (u1,lineariseVarSet cG)
    linL = (u2,lineariseVarSet dL)
\end{code}


Anything else is not handled right now;
\begin{code}
ascDischarge _ _ ascL = return [ascL]
\end{code}

\subsection{Freshness Condition  Discharge}

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
freshDischarge :: MonadFail m => [Subscript]
              -> VarSet -> VarSet -> [AtmSideCond] -> m SideCond
freshDischarge ss anteFvs cnsqFvs asc
  = do asc' <- freshDischarge' ss anteFvs asc
       return (asc' , cnsqFvs S.\\ anteFvs )
\end{code}

\begin{code}
freshDischarge' :: MonadFail m => [Subscript]
                -> VarSet -> [AtmSideCond] -> m [AtmSideCond]
freshDischarge' ss anteFvs [] = return []
freshDischarge' ss anteFvs (asc:ascs)
  = do ascl  <- freshAtomDischarge ss anteFvs asc
       ascs' <- freshDischarge'    ss anteFvs ascs
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
freshAtomDischarge :: MonadFail m => [Subscript]
                   -> VarSet -> AtmSideCond -> m [AtmSideCond]
\end{code}
We now consider the following possibilities:
\begin{eqnarray*}
   G_F \discharges D_L \disj V
   &=& \true, \quad \IF\quad D_L \subseteq G_F
\\ &\mapsto& D_L \setminus G_F \disj V
\end{eqnarray*}
\begin{code}
freshAtomDischarge ss gF (Disjoint u gv dL)
  | linL `subset` linF  =  return []
  | otherwise  =  return [gv `disjwith` (linL `diff` linF)]
  where
    subset = isSCsubset ss
    diff s t  = packUG $ doSCdiff ss s t
    linF = (NonU,lineariseVarSet gF)
    linL = (u,lineariseVarSet dL)
\end{code}

\begin{eqnarray*}
   G_F \discharges C_L \supseteq V
   &\mapsto&  C_L \setminus G_F \supseteq V
\end{eqnarray*}
\begin{code}
freshAtomDischarge ss gF (CoveredBy u gv cL)
  = return [gv `coveredby` (linL `diff` linF)]
  where
    diff s t = packUG $ doSCdiff ss s t
    linF = (NonU,lineariseVarSet gF)
    linL = (u,lineariseVarSet cL)
\end{code}


Anything else is not handled right now.
\begin{code}
freshAtomDischarge ss gF asc = return [asc]
\end{code}


\newpage
\section{Check for Floating Conditions}

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
-- we ignore uniformity here. Is this wise?
tolerateAutoOrNull unbound (Disjoint _  _ d) =  unbound `overlaps` d
tolerateAutoOrNull unbound (CoveredBy _  _ c)   =  S.null c || unbound `overlaps` c
tolerateAutoOrNull _       _              =  False
autoOrNullInAll unbound = all (tolerateAutoOrNull unbound)
\end{code}



\newpage
\section{Building side-conditions.}

Simple side-condition builders.

$\lst v \disj \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  ( [ tV `disjwith`(S.fromList vl) ], S.empty )
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  ( [ tV `coveredby` (S.fromList vl) ], S.empty )
\end{code}

$u,v,\dots \textbf{fresh.}$
\begin{code}
fresh :: VarSet -> SideCond
fresh fvs = ( [], fvs )
\end{code}

\newpage
\section{Side-condition Queries and Operations}

First, some simple queries to find atomic side-conditions of interest.
We start by checking if a variable is mentioned.
\begin{code}
findGenVar :: MonadFail m => GenVar -> SideCond -> m AtmSideCond
findGenVar gv ( ascs, _ )  =  findGV gv ascs

findGV _ [] = fail "findGenVar: not in any atomic side-condition"
findGV gv (asc:ascs)
  | gv `mentionedBy` asc  =  return asc
  | otherwise             =  findGV gv ascs

mentionedBy :: GenVar -> AtmSideCond -> Bool
gv `mentionedBy` asc
  | isUniform asc  =  gv `sameIdClass` ascGVar asc
  | otherwise      =  gv == ascGVar asc
\end{code}

We then look at returning all mentions of a variable:
\begin{code}
findAllGenVar :: GenVar -> SideCond -> [AtmSideCond]
findAllGenVar gv ( ascs, _ )  =  findAGV gv [] ascs

findAGV _ scsa []  =  reverse scsa
findAGV gv scsa (asc:ascs)
  | gv `mentionedBy` asc  =  findAGV gv (asc:scsa) ascs
  | otherwise             =  findAGV gv scsa       ascs
\end{code}

We sometimes want mentions for a specific condition type:
\begin{code}
findCoveredGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findCoveredGenVar gv ( ascs, _ ) = findCGV gv ascs

findCGV gv []        =  fail ("Covered "++show gv ++ " not found")
findCGV gv ((CoveredBy _ gv' vs):ascs)
  | gv == gv'        =  return vs
findCGV gv (_:ascs)  =  findCGV gv ascs
\end{code}

Next we develop some set queries and operations
that can handle a mix of uniform and non-uniform atomic side conditions.
We do this by comparing variables with the same identifier and class
from each side-condition.

We convert variable-sets into ordered lists of lists,
and then work through them in lock-step.
The internal lists contain all variables with the same identifier and class,
are non-empty,
and will be a singleton if the condition is uniform.
\begin{code}
lineariseVarSet :: VarSet -> [[GenVar]]
lineariseVarSet vs = lineariseVarList $ S.elems vs

lineariseVarList [] = []
lineariseVarList (gv:gvs) = lineariseVarList' gv [] gvs

lineariseVarList' gv svg [] = [ gv : svg ]
lineariseVarList' gv svg (gv':gvs)
 | gv `sameIdClass` gv' = lineariseVarList' gv (gv':svg) gvs
 | otherwise = ( gv : svg) : lineariseVarList' gv' [] gvs
\end{code}

When done, we need to pack them into a set again
\begin{code}
packVarSet :: [[GenVar]] -> VarSet
packVarSet = S.fromList . concat

packUG :: (Uniformity,[[GenVar]]) -> VarSet
packUG (_,gss) = packVarSet gss
\end{code}

\newpage
\subsection{Side-Condition Subset Query}

\begin{code}
isSCsubset :: [Subscript] -> (Uniformity,[[GenVar]]) -> (Uniformity,[[GenVar]])
           -> Bool
\end{code}

$$ \emptyset \subseteq S$$
\begin{code}
isSCsubset _ (_,[]) (_,_)      =  True
\end{code}

$$\setof{ x,\dots} \not\subseteq \emptyset$$
\begin{code}
isSCsubset _ (_,(_:_)) (_,[])  =  False
\end{code}

Given non-empty top-level lists, both will have non-empty sub-lists
(\texttt{(gv1:vl1)} and \texttt{(gv2:vl2)} below).
First, we need to walk one list or the other so that \texttt{gv1}
and \texttt{gv2} have the same identifier and class.
\begin{code}
isSCsubset ss ugs1@(u1,g1@(gv1:vl1):vls1) (u2,g2@(gv2:vl2):vls2)
  | gv1  < gv2  =  False -- remember both are ordered by id and class
  | gv1  > gv2  =  isSCsubset ss ugs1 (u2,vls2) -- move on up on right
  | otherwise  -- gv1 `sameIdClass` gv2
      = isUGsubset ss (u1,g1) (u2,g2) && isSCsubset ss (u1,vls1) (u2,vls2)
\end{code}

\begin{code}
isSCsubset ss (u1,lvl1) (u2,lvl2)  =  False
\end{code}

Subset checking given all with same identifier and class:
\begin{code}
isUGsubset :: [Subscript] -> (Uniformity,[GenVar]) -> (Uniformity,[GenVar])
           -> Bool
-- both GenVar lists are non-empty and ordered
-- all their contents have the same identifier and class
-- If ui is Uniform, then GenVar_i is a singleton
isUGsubset _  _             (Unif,[_])     =  True
isUGsubset ss (Unif,[_])    (_,vl2)        =  hasAllDynamics ss vl2
isUGsubset _  (_,vl1@(_:_)) (_,vl2@(_:_))  =  vl1 `issubset` vl2

isUGsubset _ uv1 uv2 -- should never be called
  = error $ unlines'
     [ "isUGsubset: ill-formed args"
     , "(u1,vl1) = " ++ show uv1
     , "(u2,vl2) = " ++ show uv2
     ]
\end{code}

\newpage
\subsection{Side-Condition Disjoint Query}

\begin{code}
isSCdisjoint :: [Subscript] -> (Uniformity,[[GenVar]]) -> (Uniformity,[[GenVar]])
             -> Bool
\end{code}

$$\emptyset\disj S \qquad S \disj\emptyset$$
\begin{code}
isSCdisjoint _ (_,[]) _       =  True
isSCdisjoint _ _      (_,[])  =  True
\end{code}

If both are non-empty, we walk both lists,
checking for same-id/class sub-lists and checking their disjointness.
\begin{code}
isSCdisjoint ss ugs1@(u1,g1@(gv1:vl1):vls1) ugs2@(u2,g2@(gv2:vl2):vls2)
  | gv1  < gv2  =  isSCsubset ss (u1,vls1) ugs2 -- move up on left
  | gv1  > gv2  =  isSCsubset ss ugs1 (u2,vls2) -- move up on right
  | otherwise  -- gv1 `sameIdClass` gv2
      = isUGdisjoint ss (u1,g1) (u2,g2) && isSCdisjoint ss (u1,vls1) (u2,vls2)
\end{code}

Disjoint checking given all with same identifier and class:
\begin{code}
isUGdisjoint :: [Subscript] -> (Uniformity,[GenVar]) -> (Uniformity,[GenVar])
             -> Bool
-- both GenVar lists are non-empty and ordered
-- all their contents have the same identifier and class
-- If ui is Uniform, then GenVar_i is a singleton
isUGdisjoint _   (NonU,vl1)  (NonU,vl2)  =  vl1 `isdisj` vl2
isUGdisjoint _   _           _           =  False
\end{code}

\newpage
\subsection{Side-Condition Set Difference}

\begin{code}
doSCdiff :: [Subscript] -> (Uniformity,[[GenVar]]) -> (Uniformity,[[GenVar]])
         -> (Uniformity,[[GenVar]])
\end{code}

$$S \setminus \emptyset = S \qquad \emptyset \setminus S = \emptyset$$
\begin{code}
doSCdiff _ (u1,vls1) (_,[])  =  (u1,vls1)
doSCdiff _ (u1,[])   (_,_)   =  (u1,[])
\end{code}

Otherwise, we walk through both sides
\begin{code}
doSCdiff ss ugs1 ugs2 = doSCdiff' ss [] ugs1 ugs2

doSCdiff' ss slv (u1,[]) _  =  (u1,reverse slv)

doSCdiff' ss slv (u1,vls1) (_,[]) = (u1,reverse slv ++vls1)

doSCdiff' ss slv ugs1@(u1,g1@(gv1:vl1):vls1) ugs2@(u2,g2@(gv2:vl2):vls2)
  | gv1  < gv2  =  doSCdiff' ss (g1:slv) (u1,vls1) ugs2 -- keep g1
  | gv1  > gv2  =  doSCdiff' ss slv      ugs1      (u2,vls2)
  | null g3     =  doSCdiff' ss slv      (u1,vls1) (u2,vls2)  -- gv1 ~ gv2
  | otherwise   =  doSCdiff' ss (g3:slv) (u1,vls1) (u2,vls2)  -- gv1 ~ gv2
  where
    (_,g3) = doUGdiff ss (u1,g1) (u2,g2)
\end{code}

Set difference given all with same identifier and class:
\begin{code}
doUGdiff :: [Subscript] -> (Uniformity,[GenVar]) -> (Uniformity,[GenVar])
         -> (Uniformity,[GenVar])
doUGdiff _  (u1,_)       (Unif,_)  =  (u1,[])
doUGdiff ss (Unif,[gv1]) (_,g2)    =  (NonU,genTheGenVars gv1 ss \\ g2)
doUGdiff ss (u1,g1)      (_,g2)    =  (u1,g1 \\ g2)
\end{code}

\newpage
\subsection{Side-Condition Set Intersection}

\begin{code}
doSCint :: [Subscript] -> (Uniformity,[[GenVar]]) -> (Uniformity,[[GenVar]])
         -> (Uniformity,[[GenVar]])
\end{code}

$$S \cap \emptyset = \emptyset \qquad \emptyset \cap S = \emptyset$$
\begin{code}
doSCint _ _       (_,[])  =  (NonU,[])
doSCint _ (u1,[]) _       =  (NonU,[])
\end{code}

Otherwise, we walk through both sides
\begin{code}
doSCint ss ugs1 ugs2 = doSCint' ss [] ugs1 ugs2

doSCint' ss slv (_,[]) _      =  (NonU,reverse slv)
doSCint' ss slv _     (_,[])  =  (NonU,reverse slv)

doSCint' ss slv ugs1@(u1,g1@(gv1:vl1):vls1) ugs2@(u2,g2@(gv2:vl2):vls2)
  | gv1  < gv2  =  doSCint' ss slv (u1,vls1) ugs2
  | gv1  > gv2  =  doSCint' ss slv ugs1      (u2,vls2)
  | null g3     =  doSCint' ss slv (u1,vls1) (u2,vls2)
  | otherwise   =  doSCint' ss (g3:slv) (u1,vls1) (u2,vls2)
  where
    (_,g3) = doUGunion ss (u1,g1) (u2,g2)
\end{code}

Set intersection given all with same identifier and class:
\begin{code}
doUGint :: [Subscript] -> (Uniformity,[GenVar]) -> (Uniformity,[GenVar])
         -> (Uniformity,[GenVar])
doUGint _  (u1,g1)    (Unif,[_])  =  (u1,g1)
doUGint ss (Unif,[_]) (u2,g2)     =  (u2,g2)
doUGint ss (_,g1)     (_,g2)      =  (NonU,g1 `intersect` g2)
\end{code}



\newpage
\subsection{Side-Condition Set Union}


\begin{code}
doSCunion :: [Subscript] -> (Uniformity,[[GenVar]]) -> (Uniformity,[[GenVar]])
         -> (Uniformity,[[GenVar]])
\end{code}

$$S \cup \emptyset = \S \qquad \emptyset \cup S = S$$
\begin{code}
doSCunion _ ugs1  (_,[])  =  ugs1
doSCunion _ (_,[]) ugs2   =  ugs2
\end{code}

Otherwise, we walk through both sides
\begin{code}
doSCunion ss ugs1 ugs2 = doSCunion' ss [] ugs1 ugs2

doSCunion' ss slv (_,[])   (_,vls2)  =  (NonU,reverse slv ++ vls2)
doSCunion' ss slv (_,vls1) (_,[])    =  (NonU,reverse slv ++ vls1)

doSCunion' ss slv ugs1@(u1,g1@(gv1:vl1):vls1) ugs2@(u2,g2@(gv2:vl2):vls2)
  | gv1  < gv2  =  doSCunion' ss (g1:slv) (u1,vls1) ugs2
  | gv1  > gv2  =  doSCunion' ss (g2:slv) ugs1      (u2,vls2)
  | otherwise   =  doSCunion' ss (g3:slv) (u1,vls1) (u2,vls2)
  where
    (_,g3) = doUGunion ss (u1,g1) (u2,g2)
\end{code}

Set intersection given all with same identifier and class:
\begin{code}
doUGunion :: [Subscript] -> (Uniformity,[GenVar]) -> (Uniformity,[GenVar])
         -> (Uniformity,[GenVar])
doUGunion ss ug1@(Unif,[_]) _               =  ug1
doUGunion ss _              ug2@(Unif,[_])  =  ug2
doUGunion ss (_,g1)         (_,g2)          =  (NonU,g1 `union` g2)
\end{code}





\newpage
\subsection{Dealing with Dynamics}

A check that a non-uniform \texttt{GenVar} list
mentions before-, after- and all subscripts in scope.
\begin{code}
hasAllDynamics :: [Subscript] -> [GenVar] -> Bool
-- [GenVar] is ordered  Before,During 1,..,During n,After
hasAllDynamics ss gvs  =  map gvarWhen gvs == genTheDynamics ss

genTheDynamics :: [Subscript] -> [VarWhen]
genTheDynamics ss = Before : map During ss ++ [After]

genTheGenVars :: GenVar -> [Subscript] -> [GenVar]
genTheGenVars (StdVar (Vbl i vc _)) ss
  = map (StdVar . Vbl i vc) (Before : map During ss ++ [After])
genTheGenVars (LstVar (LVbl (Vbl i vc _) is js)) ss
  = map (LstVar . mklv i vc is js) (Before : map During ss ++ [After])
  where
    mklv i vc is js vw = LVbl (Vbl i vc vw) is js
\end{code}


% First, given a variable-set,
% return all ASCs that mention any variable in that set:
% \begin{code}
% -- NOT USED ANYWHERE!
% citingASCs :: VarSet -> SideCond -> [AtmSideCond]
% citingASCs vs (sc,_) = filter (cited vs) sc
%
% cited :: VarSet -> AtmSideCond -> Bool
% vs `cited` asc  =  vs == ascVSet asc
% -- this needs rework as it uses ascVSet which is uniformity-blind
% \end{code}

\newpage

\section{SideCond Tests}

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


\subsection{Atomic Checker Tests}

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

\subsection{Merging Tests}

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

\subsection{Discharge Tests}

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


\subsection{Exported Test Group}

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
