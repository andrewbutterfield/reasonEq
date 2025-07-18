\chapter{Side Conditions}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017-2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  NVarSet, nset
, isThere, nsngl, nmbr, ndiff, nunion, nintsct, nsubset, ndisj
, VarSideConds(..)
, termVar, disjointFrom, coveredBy, coveredDynamic
, mkVSC
, vscTrue, disjNA, covByNA, isTrueVSC
, vscVSet
, disjfrom, coveredby, dyncovered, udisjfrom, ucoveredby, udyncovered
, SideCond, scTrue, isTrivialSC
, onlyFreshSC -- , onlyInvolving, onlyFreshOrInvolved
-- , scGVars
, scVarSet
, mrgVarConds, mergeVarConds, joinVarConds, concatVarConds
, mrgSideCond, mrgSideConds, mkSideCond
, scDischarge
, isFloatingVSC
, addFreshVars
, notin, covers, dyncover, fresh
, findGenVarInSC, findAllGenVar
, findDisjointGenVar, findCoveredGenVar, findDynCvrdGenVar
, mentionedBy
-- , citingASCs   -- not used anywhere!
, (.:), mrgscs
, int_tst_SideCond
) where
import Data.Char
import Data.List
import Data.Maybe (isJust, fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import NotApplicable
import YesBut
import Utilities
import LexBase
import Variables
import Types
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
In general we have a conjunction of term variable conditions,
but we need to be able to distinguish between no conditions (always ``true'')
and inconsistent conditions
(e.g. $x \disj \fv(T) \land x = \fv(T) $, always ``false'').
As a false side-condition means a match failure,
we do not represent them explicitly.
Instead, any operation on side-conditions that could result
in an inconsistent result should fail, gracefully.

NEW: the term $T$ is represented using the \texttt{StdVar} variant of a 
\texttt{GenVar}. 
However there are emerging use cases that want to relate a list-variable with a
set of general variables. 
These crop up in the UTCP theory when defining $X(E|R|a|N)$,
such as $\lst O,\lst O' \disj E$, 
or $\setof{E} \disj \lst O \land \setof{E} \disj \lst O'$, 
where $E$ is an (unknown) expression variable.

\subsection{Term (List-Variable?)/Variable-Set Relations}

An term variable side-condition (VSC) can have one of the following forms,
where $T$ abbreviates $\fv(T)$:
\begin{eqnarray*}
   x,\lst v   \disj  T
   && \mbox{disjoint, short for }\{x,\lst v\} \cap \fv(T) = \emptyset
\\ x,\lst v \supseteq T 
   && \mbox{covering, short for }\{x,\lst v\} \supseteq \fv(T)
\\ x_d,\lst v_d \supseteq_a T 
   && \mbox{dynamic coverage, short for } \{x_d,\lst v_d\} \supseteq \dfv(T)
\\ pre      \supseteq T && \mbox{pre-condition, no dashed variables}
\end{eqnarray*}
The dynamic variables here correspond to what UTP calls the ``alphabet''
of a predicate, hence the use of subscript `a'.`
For dynamic coverage, a fuller more rigorous definition is:
\begin{equation*}
V \supseteq_a T 
\quad\defs\quad 
(\forall g \in V \bullet \isdyn(g))
\land
V \supseteq \dfv(T)
\end{equation*}
We use the suffix 

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
We could also have the UTCP situation mentioned above where the term is replaced
by a list variable, which in this case represents a set of variables, not terms
(not entirely sure about this).

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
\\ \emptyset \supseteq_a z && \lnot\isdyn(z)
\\ pre       \supseteq z   && z \textrm{ is a \texttt{Before} variable}
\end{eqnarray*}
For list variables, we can add:
\begin{eqnarray*}
   \lst\ell  \supseteq \lst\ell\less x,\dots  && \true
\\ \lst\ell  \supseteq_a \lst\ell\less x,\dots  && \isdyn(\lst\ell)
\end{eqnarray*}

We also need to take account of known variables of various kinds
when evaluating and building side-conditions.

In general a given term variable $T$ could be involved 
in all three condition types:
$$
  D \disj T \land C \supseteq T \land C_d \supseteq_a T
$$
which can be normalised to
$$
  D \disj T \land 
  (C \setminus D) \supseteq T 
  \land (C_d \setminus D) \supseteq_a T
$$
We can compress this to $(T,D,C,C_d)$.

The disjoint condition is true for any variable if $D$ is null.
The coverage conditions are true if $C$ or $C_d$ cover all possible variables.
which we can capture with the idea of a universe set $U$ or $U_d$.
However doing this causes both conceptual confusion 
and results in erroneous inferences. 
A ``true'' side-condition is basically one 
that we don't consider or assess in any way.
It denotes the lack of any condition that needs to be satisfied.

We use the \h{NA} type to indicate when a component is irrelevant.

\newpage
\section{Variable Side-Conditions}

We now introduce our notion of term-variable side-conditions.
We will not represent $pre$ explicitly here,
and instead will use $\lst O \supseteq T$.

First we need to be able to say when a specific side-condition is inapplicable:

\begin{code}
type NVarSet = NA VarSet

isThere :: NVarSet -> Bool
isThere (The _)  =  True
isThere _        =  False

nsngl :: GenVar -> NVarSet
nsngl x = The $ S.singleton x


-- WE WILL NEED TO REVISIT THESE
-- USE CASE 1  - both sets have same status 
-- USE CASE 2  - set 1 is the relevant one, unchanged if set 2 is NA
nmbr :: GenVar -> NVarSet -> Bool
nmbr _ NA       =  False
nmbr x (The s)  =  x `S.member` s

ndiff :: NVarSet -> NVarSet -> NVarSet
ndiff _        NA   =  The S.empty
ndiff NA  _         =  NA -- approximation
ndiff (The s) (The t)  =  The (s `S.difference` t)

nunion :: NVarSet -> NVarSet -> NVarSet
nunion _        NA   =  NA
nunion NA  _         =  NA
nunion (The s) (The t)  =  The (s `S.union` t)

nintsct :: NVarSet -> NVarSet -> NVarSet
nintsct uset1    NA   =  uset1
nintsct NA  uset2     =  uset2
nintsct (The s) (The t)  =  The (s `S.intersection` t)

nsubset :: NVarSet -> NVarSet -> Bool
nsubset _        NA   =  False
nsubset NA  _         =  False
nsubset (The s) (The t)  =  s `S.isSubsetOf` t

ndisj :: NVarSet -> NVarSet -> Bool
NA `ndisj` _  =  False
_ `ndisj` NA  =  False
(The s) `ndisj` (The t)  =  s `S.disjoint` t
\end{code}


Now we define side-conditions for a given general variable:
\begin{code}
data  VarSideConds -- (V,D,C,Cd)
  = VSC  GenVar       --  v,T,l$
         (NA VarSet)  --  D, if applicable
         (NA VarSet)  --  C, if applicable
         (NA VarSet)  --  Cd, if applicable
  deriving (Eq, Ord, Show, Read)

termVar        :: VarSideConds -> GenVar
termVar (VSC gv nvsD nvsC nvsCd)         =  gv
disjointFrom   :: VarSideConds -> NVarSet
disjointFrom (VSC gv nvsD nvsC nvsCd)    =  nvsD
coveredBy      :: VarSideConds -> NVarSet
coveredBy (VSC gv nvsD nvsC nvsCd)       =  nvsC
coveredDynamic :: VarSideConds -> NVarSet
coveredDynamic (VSC gv nvsD nvsC nvsCd)  =  nvsCd

nset :: NVarSet -> VarSet -- partial
nset (The vs)  =  vs
nset NA        =  error "nset applied to NA"


disjNA = NA
covByNA = NA
vscTrue gv = VSC gv disjNA covByNA covByNA
isTrueVSC (VSC _ NA NA NA)  =  True
isTrueVSC _                 =  False
\end{code}

We need a smart builder here:
we first compare \h{gv} with the three sets to see
if we can deduce truth/falsity here and now;
then we check to see if everything has reduced to true.
In general we can only draw hard conclusions here if \h{gv}
occurs in any such set, 
or \h{gv} is a standard observation variable,
as are all the variables mentioned in the corresponding set.
\begin{code}
mkVSC :: MonadFail m
      => GenVar -> NVarSet -> NVarSet -> NVarSet 
      -> m (Maybe VarSideConds)
mkVSC gv nvsD nvsC nvsCd  =  do
    nvsD'  <- obviousDisj   gv nvsD 
    nvsC'  <- obviousCovBy  gv nvsC
    nvsCd' <- obviousCovBy  gv nvsCd
    if isTrue nvsD' nvsC' nvsCd'
    then return Nothing 
    else return $ Just $ VSC gv nvsD' nvsC' nvsCd'
  where
\end{code}
\begin{code}
    obviousDisj gv NA = return NA
    obviousDisj gv nvsD@(The vsD)
      |  gv `S.member` vsD               =  fail not_disjoint
      |  isObsGVar gv && allStdObsS vsD  =  return NA
      |  otherwise                       =  return nvsD 
      where not_disjoint = "gv is member of the disjoint set"
\end{code}
\begin{code}
    obviousCovBy  gv NA                  =  return NA
    obviousCovBy  gv nvsC@(The vsC)
      |  gv `S.member` vsC               =  return NA
      |  isObsGVar gv && allStdObsS vsC  =  fail not_covered
      |  otherwise                       =  return nvsC
      where not_covered = "gv is not in covering set"
\end{code}
\begin{code}
    isTrue NA        NA NA               =  True 
    isTrue (The vsD) NA NA               =  S.null vsD
    isTrue _ _ _                         =  False
\end{code}



Collecting all sets explicitly mentioned:
\begin{code}
vscVSet :: VarSideConds -> VarSet
vscVSet vsc  
  =  (asSet $ disjointFrom vsc)
     `S.union` 
     (asSet $ coveredBy vsc) 
     `S.union` 
     (asSet $ coveredDynamic vsc)
  where 
   asSet NA    =  S.empty
   asSet (The vs)  =  vs
\end{code}

We provide some builders when only one of the three conditions is involved:
\begin{code}
disjfrom, coveredby, dyncovered :: GenVar -> VarSet -> VarSideConds
gv `disjfrom`   vs  =  VSC gv (The vs) covByNA  covByNA
gv `coveredby`  vs  =  VSC gv disjNA   (The vs) covByNA
gv `dyncovered` vs  =  VSC gv disjNA   covByNA  (The vs)
udisjfrom,ucoveredby, udyncovered :: GenVar -> NVarSet -> VarSideConds
gv `udisjfrom`   NA        =  vscTrue gv
gv `udisjfrom`   (The vs)  =  gv `disjfrom`  vs
gv `ucoveredby`  NA        =  vscTrue gv
gv `ucoveredby`  (The vs)  =  gv `coveredby`  vs
gv `udyncovered` NA        =  vscTrue gv
gv `udyncovered` (The vs)  =  gv `dyncovered` vs
\end{code}


\subsection{Checking Atomic Sideconditions}

What we have are relations $R$ between a general variable $g$
and a set of general variables $V$:
\begin{eqnarray*}
   R &:& GVar \times \Set(GVar) \fun \Bool
\end{eqnarray*}

Here we provide a monadic function that fails if the condition
is demonstrably false,
and otherwise returns a \texttt{Maybe} type,
where \texttt{Nothing} denotes a condition that is demonstrably true.

\begin{code}
mscTrue = Nothing
vscCheck :: MonadFail m => VarSideConds 
          -> m (Maybe VarSideConds)
vscCheck (VSC gv nvsD nvsC nvsCd)
  = do  nvsD'  <- disjointCheck  gv nvsD
        nvsC'  <- coveredByCheck gv nvsC
        nvsCd' <- dynCvrgCheck   gv nvsCd
        mkVSC gv nvsD' nvsC' nvsCd'
\end{code}

The key trick is to take \m{g ~R~ \setof{g_1,\dots,g_n}}
and break it down into individual comparisons (\m{g ~R~ \setof{g_i}}).

\newpage
\subsubsection{Checking Disjoint $ V \disj g$}

Here, checking \m{g \disj \setof{g_1,\dots,g_n}}
reduces to checking \m{\bigwedge_{i \in 1\dots n}(g \disj g_i)}.
\begin{itemize}
  \item definitely \false : \m{g = g_i}
  \item definitely \true : \m{g} and \m{g_i} 
     are both dynamic and have different dynamicity.
\end{itemize}
\begin{code}
disjointCheck  :: MonadFail m => GenVar -> NVarSet -> m NVarSet
disjointCheck gv NA         =  return disjNA
disjointCheck gv (The vsD) = do
  checked  <-  disjCheck gv S.empty $ S.toList vsD
  return $ The checked


disjCheck :: MonadFail m
          => GenVar -> VarSet -> [GenVar] -> m VarSet
disjCheck gv vsd [] = return vsd
disjCheck gv vsd (gvd:gvs)
  | gv == gvd             =  fail "disjCheck: same variable"
  | gvw /= gvdw && bothd  =  disjCheck gv vsd                gvs
  | otherwise             =  disjCheck gv (S.insert gvd vsd) gvs
  where
    gvw = gvarWhen gv
    gvdw = gvarWhen gvd
    bothd = isDynamic gvw && isDynamic gvdw
\end{code}


\subsubsection{Checking CoveredBy $V \supseteq g$}

We may have \m{V} as the universal set, in which case  we return true.
Otherwise, we can reduce checking \m{\setof{g_1,\dots,g_n} \supseteq g}
to checking \m{\bigvee_{i \in 1,\dots,n} g = g_i \lor g \in g_i}.
However we need to keep in mind that \m{g} can denote the universal set.

\begin{code}
coveredByCheck :: MonadFail m => GenVar -> NVarSet -> m NVarSet

coveredByCheck gv NA  =  return covByNA  -- gv `coveredby` U
coveredByCheck gv jvsC@(The vsC)
  = covByCheck gv S.empty $ S.toList vsC
\end{code}
We work through the variable-set, looking for the genvar.
We remove any observables that can't match.
Failure occurs if the genvar is an observable and the ending var-set is empty.
\begin{code}
covByCheck :: MonadFail m => GenVar -> VarSet -> [GenVar] -> m NVarSet

covByCheck gv vsc []
  | S.null vsc && isObsGVar gv  = fail "covered by nothing" 
  -- term-vars,list-vars may evaluate to the empty-set, in which case this is true
  | otherwise  = return $ The vsc
covByCheck gv vsc (gvc:gvs)
  | gv == gvc       =  return covByNA 
  | lvCovBy gv gvc  =  return covByNA
  | isObsGVar gv && isObsGVar gvc  =  covByCheck gv vsc gvs
  -- if either is termvar then gv could be covered by gvs
  | otherwise       =  covByCheck gv (S.insert gvc vsc) gvs
\end{code}
Is $\ell\less V$ covered by $\kappa\less W$ ?
It is if $\ell=\kappa$ and $W \subseteq V$.
\begin{code}
lvCovBy :: GenVar -> GenVar -> Bool
lvCovBy (LstVar (LVbl v is js)) (LstVar (LVbl covv isv jsv))
  = v == covv && isv `issubset` is && jsv `issubset` js
lvCovBy _ _ = False
\end{code}


\newpage
\subsubsection{Checking DynamicCoverage $V \supseteq_a g$}


We first check that all of $V$ is dynamic:
\begin{eqnarray*}
   \exists g_i \in V \bullet \lnot\isdyn(g_i) && \false
\end{eqnarray*}
We can reduce checking \m{\setof{g_1,\dots,g_n} \supseteq g}
to checking \m{\bigvee_{i \in 1,\dots,n} g = g_i \lor g \in g_i}.

Assuming $\forall v \in V \bullet \isdyn(v)$ we then proceed:
\begin{eqnarray*}
   \emptyset             \supseteq_a z   &&  \lnot\isdyn(z)
\\ O,O' \supseteq_a V &&  
        \true, \quad \IF \quad V \subseteq O \cup O' \cup ObsV
\\ \lst\ell\setminus Z \supseteq_a \lst\ell\setminus (Z\cup W) 
                                         &&  \true
\\ \dots,g,\dots{}       \supseteq_a g   &&  \true
\\ \{stdObs\}\setminus z \supseteq_a z   &&  \false
\end{eqnarray*}

Here, as $T$ could be empty,
we cannot deduce that $\emptyset \supseteq T$ is false.
Similarly, $T \supseteq z$ could also be true.
\begin{code}
dynCvrgCheck :: MonadFail m => GenVar -> NVarSet -> m NVarSet

dynCvrgCheck gv NA  =  return covByNA
dynCvrgCheck gv jvsCd@(The vsCd)
  | notAllDyn  =  report "tvar dyncover fails (static)"
--  | otherwise  = covByCheck gv S.empty $ S.toList vsCd
  | any (lvCovBy gv) vsCd   =  return covByNA
  | not $ isObsGVar gv      =  return jvsCd
  | S.null vsCd 
      =  if isDynGVar gv
         then report "atomic dyncover fails (null)"
         else return jvsCd
  | all isStdV vsCd         =  report "tvar dyncover fails (all std)"
  where 
    notAllDyn = not $ all isDynGVar vsCd
    showsv = "gv = "++show gv
    showvs = "vsCd = "++show vsCd
    report msg = fail $ unlines' [msg,showsv,showvs]
dynCvrgCheck _ nvsCd  =  return nvsCd
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

A ``full'' side-condition is basically 
a list of term-variable side-conditions,
interpreted as their conjunction,
along with a set defining fresh variables.
\begin{code}
type SideCond = ( [VarSideConds]  -- all must be true
                , VarSet )       -- must be fresh
\end{code}

If the term variable condition list is empty,
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
onlyFreshSC (vscs,_) = null vscs
\end{code}
Finally,
sometimes we want all the variable-sets
from a side-condition:
\begin{code}
scVarSet :: SideCond -> VarSet
scVarSet (vscs,fvs) = (S.unions $ map vscVSet vscs) `S.union` fvs
\end{code}


\newpage
\section{Merging Side-Conditions}

The list of VSCs
is kept ordered by the \texttt{GenVar} component,
and any given such variable occurs at most once.
The function \texttt{mrgVarConds} below is the ``approved'' way
to generate side-conditions,
by merging them in, one at a time,
into a pre-existing list ordered and structured as described above.
\begin{code}
mrgVarConds :: MonadFail m 
            => VarSideConds -> [VarSideConds] -> m [VarSideConds]
\end{code}
\textbf{Invariant}\\
For \texttt{mrgVarConds vsc vscs} we have:\\
\texttt{vscs} is ordered, and\\
for all \texttt{vsc'} in \texttt{vscs}\\
that \texttt{vscCheck vsc' == Just vsc'}.


We start by checking the new VCS:
\begin{code}
mrgVarConds vsc vscs
  = do masc <- vscCheck vsc
       case masc of
         Nothing    ->  return vscs -- vsc is in fact true
         Just vsc'  ->  mrgVSC vsc' vscs
\end{code}

Now we search to see if there is a VSCs with the
same general-variable, respecting the ordering:
\begin{code}
mrgVSC :: MonadFail m 
       => VarSideConds -> [VarSideConds] -> m [VarSideConds]

mrgVSC vsc' []  = return [vsc']

mrgVSC vsc' vscs@(vsc1:vscs')
  | v' < v1  =  return (vsc':vscs)
  | v' > v1  =  do vscs'' <- mrgVSC vsc' vscs'
                   return ( vsc1 : vscs'' )
  | otherwise -- v' == v1
    = do  case mrgSameGVSC vsc' vsc1 of
            Nothing            -> fail "mgrTVarConds: false s.c."
            Just Nothing       -> return vscs' -- mrg is true 
            Just (Just vsc'') -> return (vsc'':vscs')
  where
    v' = termVar vsc'
    v1 = termVar vsc1
\end{code}

Finally, given a list of un-merged VSCs,  we want to merge them:
\begin{code}
mergeVarConds :: MonadFail mf => [VarSideConds] -> mf [VarSideConds]
mergeVarConds [] = return []
mergeVarConds (vsc:vscs) = mrgVSC vsc vscs
\end{code}

\subsection{Merging two (checked) VSCs}

Now, merging an VSC in with another VSC referring to the same general variable:
\begin{code}
mrgSameGVSC :: MonadFail m 
            => VarSideConds -> VarSideConds -> m (Maybe VarSideConds)
mrgSameGVSC (VSC gv nvsD1 uvsC1 uvsCd1) (VSC _ nvsD2 uvsC2 uvsCd2) 
  = let  -- merging, both sets have equal status
      nvsD'   = nvsD1  `nunion` nvsD2
      nvsC'  =  uvsC1  `nintsct` uvsC2
      nvsCd' =  uvsCd1 `nintsct` uvsCd2
    in mkVSC gv nvsD' nvsC' nvsCd'
\end{code}

Finally, something to merge lists (and lists of lists) of VSCs:
\begin{code}
joinVarConds :: MonadFail m 
             => [VarSideConds] -> [VarSideConds] -> m [VarSideConds]
joinVarConds vscs1 [] = return vscs1
joinVarConds vscs1 (vsc2:vscs2) = do
  vscs1' <- mrgVSC vsc2 vscs1
  joinVarConds vscs1' vscs2
concatVarConds :: MonadFail m => [[VarSideConds]] -> m [VarSideConds]
concatVarConds [] = return []
concatVarConds [vscs] = return vscs
concatVarConds (vscs1:vscs2:vscss) = do
  vscs' <- joinVarConds vscs1 vscs2
  concatVarConds (vscs':vscss)
\end{code}

\newpage
\subsection{VSC Merge Laws}

We have the following interactions,
where $D$ and $C$ are the variable-sets found
in \texttt{Disjoint} and \texttt{CoveredBy} respectively.
So the semantics of the disjoint ($D$), covering ($C$),
and dynamic covering ($C_d$) variable-sets,
parameterised by a general variable $G$,
are:
\begin{eqnarray*}
  \sem{\_}_{\_} &:& \power V \fun V \fun \Bool
\\ \sem{D}_G &=& \fv.G \cap D = \emptyset
\\ \sem{C}_G &=& \fv.G \subseteq C
\\         &=& \fv.G = \emptyset, \quad \IF \quad C = \emptyset
\\ \sem{C_d}_G &=& \dfv.G \subseteq C \land \forall_{\isdyn}(C)
\\             &=& \dfv.G = \emptyset, \quad \IF \quad C = \emptyset
\end{eqnarray*}
We get the following (fairly obvious) laws:
\begin{eqnarray*}
   \sem{D_1}_G \land \sem{D_2}_G &=&  \sem{D_1 \cup D_2}_G
\\ \sem{C_1}_G \land \sem{C_2}_G &=&  \sem{C_1 \cap C_2}_G
\\ \sem{C1_d}_G \land \sem{C2_d}_G &=&  \sem{(C1 \cap C2)_d}_G
\\ \sem{D}_G \land \sem{C}_G
   &=&  \sem{D}_G \land \sem{C \setminus D}_G
\\ &=& \fv.G = \emptyset, \quad \IF \quad C\setminus D = \emptyset
\\ \sem{D}_G \land \sem{C_d}_G
   &=&  \sem{D}_G \land \sem{(C \setminus D)_d}_G
\\ &=& \fv.G = \emptyset, \quad \IF \quad C\setminus D = \emptyset
\end{eqnarray*}
Combining the two coverage conditions goes as follows:
\begin{eqnarray*}
\lefteqn{\sem{C1}_G \land \sem{C2_d}_G}
\\ &=& \fv.G \subseteq C1
       \land
       \dfv.G \subseteq C2 \land \forall_{\isdyn}(C2)
\end{eqnarray*}
There is no simple simplication of this.
So we have the following 3-way rule:
\begin{eqnarray*}
   \sem{D}_G \land \sem{C1}_G \land \sem{C2_d}_G
   &=&  \sem{D}_G \land 
        \sem{C1 \setminus D}_G \land \sem{(C2 \setminus D)_d}_G
\\ &=& \fv.G = \emptyset, \quad\IF\quad (C1 \cup C2) \setminus D = \emptyset
\end{eqnarray*}

We note that an apparent contradiction between $D$ and $C$ (when $D \supseteq C$)
becomes an assertion that $G$ is closed.
For any given general variable $G$,
these laws ensure that we can arrange matters so that $D$ and $C$ are disjoint.

It is instructive to ask when each of the three conditions 
is (trivially?) $\true$:
\begin{eqnarray*}
   \sem{\emptyset}_G &=& \fv.G \cap \emptyset = \true
\\ \sem{U}_G &=& \fv.G \subseteq U = \true
\\ \sem{U_d}_G &=& \dfv.G \subseteq U_d \land \forall_{\isdyn}(U_d) = \true
\end{eqnarray*}
Here $U$ ($U_d$) is the set of all variables (all dynamic variables) in play.
This allows us to represent all term variable side-conditions regarding general variable $G$ as:
\begin{equation*}
\sem{D}_G \land \sem{C}_G \land \sem{C_d}_G
\quad\text{or}\quad
(G,D,C,C_d)
\end{equation*}



It is worth noting side conditions currently in use:
\begin{description}
  \item[Forall/Exists]~\\
     $\lst x \disj P \qquad \lst x \disj e \qquad \lst y \disj P$
   \item[UClose]~\\
    $\lst x \supseteq P \qquad \emptyset \supseteq P$
  \item[UTPNaiveWhile]~\\
    $
      \lst O,\lst O' \supseteq_a P
      \quad
      \lst O,\lst O' \supseteq_a Q
      \quad
      \lst O,\lst O' \supseteq_a R
    $ \\
    $
      \lst O \supseteq b
      \quad
      \lst O \supseteq e
      \quad
      \lst O \supseteq f
      \quad
      \lst O \supseteq x
      \qquad
      O_0 \textrm{ fresh}
     $
\end{description}



\subsection{Merging Term-Var Side-Condition Lists}

We check for side-conditions that are trivially true,
as sometimes these result from instantiating law side-conditions
with match bindings.
\begin{code}
mrgTVarCondLists :: MonadFail m 
                 => [VarSideConds] -> [VarSideConds] -> m [VarSideConds]
mrgTVarCondLists vscs1 []  =  return vscs1
mrgTVarCondLists [] vscs2  =  return vscs2
mrgTVarCondLists (vsc:vscs1) vscs2
  | isTrueVSC vsc  =  mrgTVarCondLists vscs1 vscs2
  | otherwise = do 
      vscs2' <- mrgVarConds vsc vscs2 
      mrgTVarCondLists vscs1 vscs2'
\end{code}

\subsection{Merging Term Variable and Freshness Side-Conditions}


\begin{code}
mrgTVarFreshConditions :: MonadFail m 
                       => VarSet -> [VarSideConds] 
                       -> m SideCond
mrgTVarFreshConditions freshvs vscs
  | freshvs `disjoint` coveredVarsOf vscs  =  return (vscs,freshvs)
  -- the above might not work - `disjoint` may need more information
  | otherwise  =  fail "Fresh variables cannot cover terms."

coveredVarsOf :: [VarSideConds] -> VarSet
coveredVarsOf vscs = S.unions $ map coveringsOf vscs
coveringsOf (VSC _ _ nvsC nvsCd)  =  cvr nvsC `S.union` cvr nvsCd
cvr NA    =  S.empty -- universe does not contain fresh vars
cvr (The vs)  =  vs
\end{code}

\section{From VSC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: MonadFail m 
           => [VarSideConds] -> VarSet -> m SideCond
mkSideCond vscs fvs
 = do vscs' <-  mrgTVarCondLists vscs []
      mrgTVarFreshConditions fvs $ filter (not . isTrueVSC) vscs'
\end{code}


\subsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each VSC and fresh set from the one into the other,
one at a time.
\textbf{Note: \h{mrgSideCond} is NOT commutative, and can be lossy}.
\begin{code}
mrgSideCond :: MonadFail m 
            => SideCond -> SideCond -> m SideCond
mrgSideCond (vscs1,fvs1) (vscs2,fvs2)
     = do vscs' <- mrgTVarCondLists vscs1 vscs2
          mrgTVarFreshConditions (fvs1 `S.union` fvs2) vscs'
          -- the above may require a obsv-savvy union?

mrgSideConds :: MonadFail m => [SideCond] -> m SideCond
mrgSideConds []        = return ([],S.empty)
mrgSideConds (sc:scs)
  | isTrivialSC sc  =  mrgSideConds scs
  | otherwise       =  do scs' <- mrgSideConds scs ; mrgSideCond sc scs'
\end{code}

\subsection{Side-Condition Operators}

We want some shorthands for assembling side-conditions,
that are also ``total'',
in that they return \texttt{SideCond} rather than \texttt{m SideCond}.
\begin{code}
mrgscs :: [SideCond] -> SideCond
mrgscs = fromJust . mrgSideConds
(.:) :: SideCond -> SideCond -> SideCond
sc1 .: sc2 = mrgscs [sc1,sc2]
\end{code}
\textbf{
These are unsafe and should only be used for the definition of 
builtins or tests.
}


\newpage
\section{Discharging Side-conditions}

We start with some examples that arise from key theories:
\begin{description}
  \item[ForAll.forall\_remove]
    Instantiated Replacement = $\lnot P$ \newline
    Instantiated Law S.C. = $\lst x \disj P$ \newline
    Goal S.C. = $\lst x \disj P$ \newline
    Discharged Law S.C. = $\top$  (CORRECT)
  \item[ForAll.forall\_one\_point]
    Instantiated Replacement = $\forall \lst y \bullet (\lnot P)[\lst e/\lst x]$ \newline
    Instantiated Law S.C. = $\lst x \disj \lst e$ \newline
    Goal S.C. = $\lst x \disj \lst e$ \newline
    Discharged Law S.C. = $\top$  (CORRECT)
  \item[UClose.{[}{]}\_def]
    Instantiated Law S.C. = $?\lst x\supseteq P$  \newline
    Goal S.C. = $\emptyset\supseteq P$ \newline
    Discharged Law S.C. = $?\lst x\supseteq P$.
    From $\emptyset \supseteq P$ we should be able to conclude 
    that $A \supseteq P$ for any arbitrary set $A$.
  \item[UTCP.X\_X\_comp]~
    Instantiated Law S.C. = $ls_1 \disj N1, ls_1 \disj R1$ \newline
    Goal S.C.: \newline
    $\lst O,\lst O' \disj E1, \lst O,\lst O' \disj E2, \lst O,\lst O' \disj N1, \lst O,\lst O' \disj N2, \lst O,\lst O' \disj R1, \lst O,\lst O' \disj R2,$ \newline
    $s,s' \supseteq_a a, s,s' \supseteq_a b, fresh:\lst O_1$ \newline
    Discharged Law S.C. = $\top$.
    From $fresh:\lst O_1$ we deduce $fresh: ls_1,s_1$,
    and should immediately be able to say that therefore $ls_1 \notin N1,R1$.
    \newline
    We also know that $\lst O = \setof{s,ls}$ (homogeneous),
    which then means that $s_1$ and $ls_1$ are fresh.
  \item[UTCP.X\_X\_comp]~
    Instantiated Law S.C. = $\lst O' \disj a$ \newline
    Goal S.C.: \newline
    $\lst O,\lst O' \disj E1, \lst O,\lst O' \disj E2, \lst O,\lst O' \disj N1, \lst O,\lst O' \disj N2, \lst O,\lst O' \disj R1, \lst O,\lst O' \disj R2,$ \newline
    Discharged Law S.C. = $\bot$ (FALSE):
    $\lst O=\setof{ls,s} \land \setof{s,s'} \supseteq_a  a 
     \not\implies 
     \lst O' \disj a$.
     It implies $\lnot(\lst O' \disj a)$, because $s \in a$.
  \item[UTCP.X\_X\_comp]~
    Instantiated Law S.C. =  % s∉E1, s∉E2, s∉N1, s∉N2, s∉R1, s∉R2, s∉ls, s∉ls'
    $s \disj E1,E2,N1,N2,R1,R2,ls,ls'$
    \newline
    Goal S.C. =  % ls,ls',s,s'∉E1, ls,ls',s,s'∉E2, ls,ls',s,s'∉N1, ls,ls',s,s'∉N2, ls,ls',s,s'∉R1, ls,ls',s,s'∉R2, s,s'⊇ₐa, s,s'⊇ₐb, fresh:ls_1,s_1
    $ls,ls,s,s \disj E1,E2,N1,N2,R1,R2, s,s \supseteq_a a,b, fresh: ls_1,s_1$
    \newline
    Discharged Law S.C. = $s \disj ls,ls'$ (INCORRECT) \newline
    Should be $\top$.
\end{description}
General comment about freshness: 
if $fresh: f$, 
and term-variable $N$ occurs in the goal, and is not under a substitution 
of the form $[f/\_]$,
then $f \disj N$ holds.

We need a gallery of ``interesting'' side-conditions:
\begin{mathpar}
   fresh: \lst O_1 \land 
   \lst O = \setof{ls,s} 
   \implies 
   ls_1 \notin T 
          \mapsto \top
\\ fresh: \lst O_1 \land 
   \lst O = \setof{ls,s} 
   \implies 
   ls_1 \subseteq T \mapsto  \bot
\\ \lst O = \setof{ls,s} \land 
   s,s' \supseteq_a a 
   \implies 
   \lst O' \disj a \mapsto \bot \qquad (\lst O' \cap a = \setof{s'})
\end{mathpar}


Here we simply check validity of $sc'_G \implies sc'_L$,
where $sc'_G$ is the goal side-condition,
and $sc'_L$ is the law side-condition translated into goal ``space''
after a successful match.
Because we may be handing side-conditions with ``questionable'' variables,
we attempt to return a simplified side-condition
that has the questionable bits \emph{that are not dischargeable}.
If we discover a contradiction,
then we need to signal this,
because \texttt{SideCond} cannot represent a false side-condition explicitly.
\begin{code}
scDischarge :: MonadFail m 
            => VarSet -> SideCond -> SideCond -> m SideCond
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

Note that the freshness criteria may only be partly resolved here,
and its final resolution will require examining the free variables 
of the goal.

This is the first point in matching where the expanded known observables
are available, as variable \texttt{obsv}.
We first simplfiy the consequence 

\begin{code}
scDischarge obsv anteSC@(anteVSC,anteFvs) cnsqSC@(cnsqVSC,cnsqFvs)
  = if isTrivialSC cnsqSC then return scTrue
    else if isTrivialSC anteSC then return cnsqSC
    else do vsc' <- scDischarge' obsv anteVSC cnsqVSC
            freshDischarge obsv anteFvs cnsqFvs vsc'
\end{code}

% \begin{code}    
% instFreshObsV :: VarSet -> VarSet -> VarSet
% instFreshObsV obsv freshvs 
%   =  S.unions $ S.map (instFreshO obsv) freshvs

% instFreshO :: VarSet -> GenVar -> VarSet
% instFreshO obsv fresh = S.unions $ S.map (instFreshV fresh) obsv

% instFreshV :: GenVar -> GenVar -> VarSet
% instFreshV fresh obs  
%   | gvarWhen obs `elem` [Before,After] && isDuring freshd 
%                =  S.singleton $ setGVarWhen freshd obs 
%   | otherwise  =  S.empty
%   where freshd = gvarWhen fresh

% vscMrg [] = return []
% vscMrg (vsc:vscs) = mrgVarConds vsc vscs    
% \end{code}

\subsection{Term-Variable  Condition  Discharge}

Now onto processing those ordered Term-Variable Side-Conditions:
\begin{code}
scDischarge'  :: MonadFail m => VarSet
              -> [VarSideConds] -> [VarSideConds]
              -> m [VarSideConds]
scDischarge' _ _ []      =  return []     --  discharged
scDischarge' _ [] vscL  =  return vscL  --  not discharged
scDischarge' obsv        (vscG@(VSC gvG _ _ _):restG) -- ante
                   vscLs@(vscL@(VSC gvL _ _ _):restL) -- cnsq
  | gvG < gvL  =  scDischarge' obsv restG vscLs -- vscG not needed
  | gvG > gvL  =  do -- nothing available to discharge vscL
                     rest' <- scDischarge' obsv restG restL
                     return (vscL:rest')
  | otherwise  =  do -- use vscG to discharge vscL
                     vsc' <- vscDischarge obsv vscG vscL
                     vscChecked <- vscCheck vsc'
                     case  vscChecked of
                       Nothing ->  scDischarge' obsv restG restL
                       Just vsc'' -> do
                         rest' <- scDischarge' obsv restG restL
                         return (vsc'':rest')
\end{code}

\newpage
\subsubsection{VSC Discharge}

At this point we have the form, for given term-variable $T$:
\begin{equation}
 \left( D_G \disj T \land C_G \supseteq T \land Cd_G \supseteq_a T \right)
 \vdash
 \left( D_L \disj T \land C_L \supseteq T \land Cd_L \supseteq_a T \right)
\end{equation}
Finally, we have arrived at where the real work is done.

\begin{code}
vscDischarge  :: MonadFail m 
              => VarSet
              -> VarSideConds -> VarSideConds 
              -> m VarSideConds
\end{code}


We use $V$ to denote the general variable,
which represents some set of (other) variables.
We have a situation where we may be able to discharge,
or falsify, but also have the possibility of being unable to do either.
This may result in the side-condition being retained,
perhaps ``reduced'' to some degree.
We use the notation $G \discharges L \mapsto R$
to say that $G$ being true means that we can simplify $L$ to a ``residual'' $R$.
We also have a set of all variables ($DO$) that are known dynamic observables
For example, given $O,O' \supseteq_a ls$, and knowlege that $ls \in O$,
we should be able to reduce this to true.
\begin{eqnarray*}
   O,O' \supseteq_a v &=& v \in O \lor v \in O'
\\ O,O' \supseteq v &=& v \in O \lor v \in O'
\end{eqnarray*}

The following cases need special treatment:

A translated law side-condition of the form $\emptyset \supseteq v$,
where $v$ is a standard variable.
This is simply false.
\begin{code}
vscDischarge _ _ (VSC (StdVar (Vbl _ ObsV _)) _ (The vsC) _)
  | S.null vsC  =  fail ("Empty set cannot cover a standard obs. variable")
\end{code}

\newpage
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
\\&=& O_m \disj (O \cup O')\mbox{, set theory}
\\ && \true
\\
O \cup O' \supseteq V &\discharges& O_m \disj V \text{, for any }m
\end{eqnarray*}
This is subsumed by the
$C_G \supseteq V \discharges D_L \disj V $
discharge rule further below.

Another case is $\lst O,\lst O' \disj N \implies ls_1 \disj N$,
given that $ls \in \lst O$. 
We cannot immediately assume it's true as the antecedent doesn't prevent
$ls_1 \in N$. However, if $ls_1$ is fresh, this will be the case.

Yet another case is $\emptyset \supseteq P \implies A \supseteq P$ 
for \emph{any} $A$.

The plan is that we first use each component (\m{D,C,Cd}) of the goal
to simplify the corresponding instantiated law components.
Then we look at the  crossovers.
We start with the \m{C} and \m{Cd} components because $\subseteq$
is strong enough to potentially falsify some side-conditions, 
whereas $\disj$ is too weak for this.

\begin{code}
vscDischarge obsv (VSC gv nvsDG nvsCG nvsCdG) (VSC _ nvsDL nvsCL nvsCdL)
  = do  nvsC'    <- ccDischarge obsv gv nvsCG  nvsCL
        nvsCd'   <- ccDischarge obsv gv nvsCdG nvsCdL
        nvsD'    <- ddDischarge obsv gv nvsDG  nvsDL

        nvsD''   <- cdDischarge obsv gv nvsCG  nvsD'
        nvsD'''  <- cdDischarge obsv gv nvsCdG nvsD''

        nvsC''   <- dcDischarge obsv gv nvsDG  nvsC'

        nvsCd''  <- dcDischarge obsv gv nvsDG  nvsCd'
        case mkVSC gv nvsD''' nvsC'' nvsCd'' of
          Nothing          ->  fail "vsc-dishcarged failed"
          Just Nothing     ->  return $ vscTrue gv
          Just (Just vsc)  ->  return vsc
\end{code}

\newpage
\subsubsection{Pairwise Discharging (C:C)}
General idea: 
\newline
  \m{C_G \supseteq V} discharges \m{C_L \supseteq V} if \m{C_G \subseteq C_L}
\newline
  \m{C_G \supseteq V} falsifies \m{C_L \supseteq V} if \m{C_G \disj C_L}

Edge cases:
\newline
  If \m{V} is a term variable, 
  then it is possible that \m{\fv(V)=\emptyset},
  in which case the fact that \m{C_G \disj C_L} is irrelevant.
\begin{eqnarray*}
   \_ \discharges C_L \supseteq V
   & = & C_L \supseteq V
\\ C_G \supseteq V \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad C_G \subseteq C_L
\\ & = & \false, \quad \IF \quad C_G \disj C_L \land isObsVar(V)
\\ & = & (C_G \cap C_L)\cup C_{?L} \supseteq V, \quad \textbf{otherwise}
\end{eqnarray*}
\begin{code}
ccDischarge :: MonadFail m 
            => VarSet -> GenVar -> NVarSet -> NVarSet 
            -> m NVarSet
ccDischarge _  _  _  NA     =  return NA
ccDischarge _  _  NA uvsCL  =  return uvsCL
ccDischarge obsv gv (The vsCG) tvsCL@(The vsCL)
  -- | S.null vsCG               =  return tvsCL
  | vsCG `S.isSubsetOf` vsCL  =  return NA -- discharged!
  | vsCL `S.disjoint` vsCG 
    && isObsGVar gv           =  fail "CC - disjoint coverage"
  | otherwise  =  return $ The ((vsCG `S.intersection` vsCL) `S.union` vsCLf)
  where vsCLf = S.filter isFloatingGVar vsCL
\end{code}

\subsubsection{Pairwise Discharging (D:D)}
General idea (assuming \m{D_G \supset \emptyset}):
\newline
\m{D_G \disj V} discharges \m{D_L \disj V} if \m{D_L \subseteq D_G}

Edge cases: \m{D_G = \emptyset} means no change to law s.c.
\newline
\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true
         \quad\cond{D_L \subseteq D_G}\quad (D_L\setminus D_G) \disj V
\end{eqnarray*}
\begin{code}
ddDischarge :: MonadFail m 
            => VarSet -> GenVar -> NVarSet -> NVarSet 
            -> m NVarSet
ddDischarge _    _  _     NA     =  return NA
ddDischarge _    _  NA    nvsDL  =  return nvsDL
ddDischarge obsv gv (The vsDG) tvsDL@(The vsDL) 
  | S.null vsDG                  =  return tvsDL
  | vsDL `S.isSubsetOf` vsDG     =  return NA -- discharged!
  | otherwise                    =  return $ The (vsDL S.\\ vsDG)
\end{code}

\newpage
\subsubsection{Pairwise Discharging (C:D)}
General idea (assuming \m{C_G \supset \emptyset}): 
\newline
  \m{C_G \supseteq V} discharges \m{D_L \disj V} if \m{C_G \disj D_L}
\newline
  \m{C_G \supseteq V} falsifies \m{D_L \disj V} if \m{C_G \subseteq D_L}
\newline
  The outcome becoems \m{(D_L \cap C_G)\disj V} if neither of the above apply
  (any \m{V} inside \m{D_L} but not in \m{C_G} are not relevant).

Edge cases:
\newline
  \m{C_G = \emptyset} discharges \m{D_L \disj V} 
  because it implies \m{\fv(V)=\emptyset}
\newline
  If \m{V} is a term variable, 
  then it is possible that \m{fv(V)=\emptyset},
  in which case the fact that \m{C_G \subseteq D_L} is irrelevant.
\begin{eqnarray*}
   \_ \discharges D_L \disj V
   & = & D_L \disj V
\\ C_G \supseteq V \discharges D_L \disj V
   & = & \true, \quad \IF \quad C_G \disj D_L
\\ & = & \false, \quad \IF \quad C_G \subseteq D_L \land isObsVar(V)
\\ & = & (D_L \cap C_G)\disj V, \quad \textbf{otherwise}
\end{eqnarray*}

\begin{code}
cdDischarge :: MonadFail m 
            => VarSet -> GenVar -> NVarSet -> NVarSet 
            -> m NVarSet
cdDischarge _    _  _  NA     =  return NA
cdDischarge obsv gv NA nvsDL  =  return nvsDL
cdDischarge obsv gv (The vsCG) tvsDL@(The vsDL)
  | S.null vsCG               =  return tvsDL
  | vsCG `S.disjoint` vsDL    =  return NA -- discharged !
  | vsCG `S.isSubsetOf` vsDL 
    && isObsGVar gv           =  fail "CD - obs cover under disjoint"
  | otherwise                 =  return $ The (vsDL `S.intersection` vsCG)
\end{code}

\subsubsection{Pairwise Discharging (D:C)}
General idea (assuming \m{D_G \supset \emptyset}):
\newline
\m{D_G \disj V} falsifies \m{C_L \supseteq V} if \m{C_L \subseteq D_G}
and \m{V} is an observable.

Edge cases: \m{D_G = \emptyset} means no change to law s.c.
\newline


\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false
         \quad\cond{C_L \subseteq D_G \land isObsVar(V)}\quad
         (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
\begin{code}
dcDischarge :: MonadFail m 
            => VarSet -> GenVar -> NVarSet -> NVarSet 
            -> m NVarSet
dcDischarge _    _  _     NA     =  return NA
dcDischarge obsv gv NA    nvsCL  =  return nvsCL
dcDischarge obsv gv (The vsDG) tvsCL@(The vsCL)
  | S.null vsDG                  =  return tvsCL
  | vsCL `S.isSubsetOf` vsDG 
    && isObsGVar gv              =  fail "DC - obs cover under disjoint"
  | otherwise                    =  return $ The (vsCL S.\\ vsDG)
\end{code}

\newpage
\subsection{Freshness Condition  Discharge}

We have reduced our original problem down to:
$$
 \fresh G_F
 \vdash
 \left( D_L \disj T 
 \land C_L \supseteq T 
        \land Cd_L \supseteq_a T 
        \land \fresh L_F  
 \right)
$$
The solution is
$$
 \left( D'_L \disj T 
 \land C'_L \supseteq T 
        \land Cd'_L \supseteq_a T 
        \land \fresh (L_F \setminus G_F)  
 \right)
$$
where elements of $G_F$ can be used to satisfy some $\setof{D,C,Cd}_L$,
resulting in modified versions $\setof{D',C',Cd'}_L$.

\textbf{NOTE:}
\textsf{
We need to use freshness to show fresh-vars as being disjoint from
any pre-existing ``sets``.
For example, 
$$
\lst O,\lst O' \disj N \land x \in \lst O
\land \fresh{\lst O_d}
\implies
x_d \disj N
$$
}

\begin{code}
freshDischarge :: MonadFail m 
               => VarSet -> VarSet -> VarSet -> [VarSideConds] 
               -> m SideCond
freshDischarge obsv anteFvs cnsqFvs vsc
  = do vsc' <- freshDischarge' obsv anteFvs vsc
       return (vsc' , cnsqFvs S.\\ anteFvs )
\end{code}

\begin{code}
freshDischarge' :: MonadFail m 
                => VarSet -> VarSet -> [VarSideConds] 
                -> m [VarSideConds]
freshDischarge' obsv anteFvs [] = return []
freshDischarge' obsv anteFvs (vsc:vscs)
  = do ascl   <- freshTVarDischarge obsv anteFvs vsc
       vscs' <- freshDischarge'    obsv anteFvs vscs
       return (ascl++vscs')
\end{code}

We use a set of fresh variables ($G_F$)
to try to discharge an term variable side-condition ($L_j$):
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
freshTVarDischarge :: MonadFail m 
                   => VarSet -> VarSet -> VarSideConds 
                   -> m [VarSideConds]
\end{code}
Given
\[G_F \discharges (D \disj V,C \supseteq V,Cd \supseteq_a V)\]
we can simplify the discharge portion of this to 
\[( D\setminus G_F \disj V
  , C\setminus G_F \supseteq V
  , Cd\setminus G_F \supseteq_a V )\]
based on the idea that $G_F \disj V$ by construction
(it's what it means for be fresh!).
\begin{eqnarray*}
   G_F \discharges D_L \disj V
   &=& \true, \quad \IF\quad D_L \subseteq G_F
\\ &\mapsto& D_L \setminus G_F \disj V
\\ G_F \discharges C_L \supseteq V
   &\mapsto&  C_L \setminus G_F \supseteq V
\\ G_F \discharges Cd_L \supseteq_a V
   &\mapsto&  Cd_L \setminus G_F \supseteq_a V
\end{eqnarray*}
\begin{code}
freshTVarDischarge obsv gF (VSC gv nvsD nvsC nvsCd) = do
  let nvsgF = The gF
  let nvsD' = nvsD `ndiff` nvsgF
  let nvsC' = nvsC `ndiff` nvsgF
  let nvsCd' = if gv `S.member` obsv then nvsCd `ndiff` nvsgF else NA
  case mkVSC gv nvsD' nvsC' nvsCd' of
    Nothing  ->  fail "fresh-var s.c. discharge failed"
    Just Nothing -> return []
    Just (Just vsc')  ->  return [vsc']
\end{code}
  % | vsc' == vscTrue gv  =  return []
  % | otherwise  =  return [vsc']
  % where
  %   nvsgF = The gF
  %   nvsD' = nvsD `ndiff` nvsgF
  %   nvsC' = nvsC `ndiff` nvsgF
  %   nvsCd' = if gv `S.member` obsv
  %            then nvsCd `ndiff` nvsgF
  %            else NA
  %   vsc' = case mkVSC gv nvsD' nvsC' nvsCd' of
  %            Nothinh
  %            Nothing   ->  vscTrue gv
  %            Just vsc  ->  vsc


\newpage
\section{Check for Floating Conditions}

When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check that \emph{all} the term variable side-conditions in that residual
mention variables that are marked as ``floating''.
Only these can possibly be instantiated to satisfy the residual side-condition.
\begin{code}
isFloatingVSC :: VarSideConds -> Bool
isFloatingVSC (VSC  gv nvsD nvsC nvsCd)
  = isFloatingGVar gv 
      || hasFloatingM nvsD || hasFloatingM nvsC || hasFloatingM nvsCd 
hasFloating :: VarSet -> Bool
hasFloating vs = any isFloatingGVar $ S.toList vs
hasFloatingM :: NVarSet -> Bool
hasFloatingM NA = False
hasFloatingM (The vs) = hasFloating vs
\end{code}
% One exception to this, during law matching,
% is that coverage may reduce to the empty set
% because unbound variables given a temporary binding
% to a ``?'' variable (\texttt{bindFloating})
% will not cancel out other variables that they should be able to do,
% if instantiated properly.
% \begin{code}
% tolerateAutoOrNull :: VarSet -> VarSideConds -> Bool
% tolerateAutoOrNull unbound (VSC _ vsD nvsC nvsCd) 
% =  unbound `overlaps` vsD
% tolerateAutoOrNull unbound (CoveredBy _  _ c)   =  S.null c || unbound `overlaps` c
% tolerateAutoOrNull _       _              =  False
% autoOrNullInAll unbound = all (tolerateAutoOrNull unbound)
% \end{code}

\section{Add Generated Fresh Variables}

Later proof steps need to know this has happened\dots

\begin{code}
addFreshVars :: VarSet -> SideCond -> SideCond
addFreshVars freshlynew (vscs,freshv) = (vscs,freshlynew `S.union` freshv)
\end{code}


\newpage
\section{Building side-conditions.}

Simple side-condition builders.

$\lst v \disj \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  ( [ tV `disjfrom`(S.fromList vl) ], S.empty )
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  ( [ tV `coveredby` (S.fromList vl) ], S.empty )
\end{code}

$\lst v \supseteq_a \fv(T)$
\begin{code}
dyncover :: VarList -> GenVar -> SideCond
vl `dyncover` tV  =  ( [ tV `dyncovered` (S.fromList vl) ], S.empty )
\end{code}

$u,v,\dots \textbf{fresh.}$
\begin{code}
fresh :: VarSet -> SideCond
fresh fvs = ( [], fvs )
\end{code}

\newpage
\section{Side-condition Queries and Operations}

First, some simple queries to find term variable side-conditions of interest.
We start by checking if a variable is mentioned.
\begin{code}
findGenVarInSC :: MonadFail m => GenVar -> SideCond -> m VarSideConds
findGenVarInSC gv ( vscs, _ )  =  findGV gv vscs

findGV _ [] = fail "findGenVarInSC: not in any term variable side-condition"
findGV gv (vsc:vscs)
  | gv == termVar vsc  =  return vsc
  | otherwise          =  findGV gv vscs
\end{code}

We then look at returning all mentions of a variable:
\begin{code}
findAllGenVar :: GenVar -> SideCond -> [VarSideConds]
findAllGenVar gv ( vscs, _ )  =  findAGV gv [] vscs

findAGV _ scsa []  =  reverse scsa
findAGV gv scsa (vsc:vscs)
  | gv == termVar vsc  =  findAGV gv (vsc:scsa) vscs
  | otherwise          =  findAGV gv scsa       vscs
\end{code}

We sometimes want mentions for a specific condition type:

For disjointness we look for precisely the given general variable.
\begin{code}
findDisjointGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findDisjointGenVar gv ( vscs, _ ) = findDGV gv vscs

findDGV gv []         =  fail ("Disjoint "++show gv ++ " not found")
findDGV gv ((VSC gv' (The vsD) _ _):vscs)
  | gv == gv' && not (S.null vsD)  =  return vsD
findDGV gv (_:vscs)                =  findDGV gv vscs
\end{code}

For regular coverage we look for precisely the given general variable,
while for dynamic coverage we ignore differences in temporality.
\begin{code}
findCoveredGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findCoveredGenVar gv ( vscs, _ ) = findCGV gv vscs

findCGV gv []           =  fail ("Covered "++show gv ++ " not found")
findCGV gv ((VSC gv' _ (The vs) _):vscs)
  | gv == gv'           =  return vs
findCGV gv ((VSC gv' _ _ (The vs)):vscs)
  | gv == gv'           =  return vs
findCGV gv (_:vscs)     =  findCGV gv vscs
\end{code}

For dynamic coverage we don't care about temporality,
but do report what temporality was found.
\begin{code}
findDynCvrdGenVar :: MonadFail m => GenVar -> SideCond -> m ( NVarSet, VarWhen )
findDynCvrdGenVar gv ( vscs, _ ) = findDCGV gv vscs

findDCGV gv []         =  fail ("DynCovered "++show gv ++ " not found")
findDCGV gv ((VSC gv' _ _ uvs):vscs)
  = case gv `dynGVarEq` gv' of
      Just vw'  ->  return (uvs, vw')
      Nothing   ->  findDCGV gv vscs
\end{code}

We have a catch-all :
\begin{code}
mentionedBy :: MonadFail m 
            => GenVar -> [VarSideConds] -> m ( VarSideConds, Maybe VarWhen)
gv `mentionedBy` []  =  fail ("variable "++show gv++" not mentioned")
gv `mentionedBy` (vsc@(VSC gv' _ _ nvsCd):vscs)
  | gv == gv'       =  return ( vsc, Nothing )
  | isThere nvsCd -- we need an explicit mention of gv'
      = case gv `dynGVarEq` gv' of
          Just vw'  ->  return ( vsc, Just vw')
          _         ->  gv `mentionedBy` vscs
  | otherwise       =   gv `mentionedBy` vscs
\end{code}


We convert variable-sets into ordered lists of lists,
and then work through them in lock-step.
The internal lists contain all variables with the same identifier and class,
are non-empty.
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

packUG :: [[GenVar]] -> VarSet
packUG (gss) = packVarSet gss
\end{code}

\newpage
\subsection{Dealing with Dynamics}

\textbf{NOT USED ANYWHERE!}
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
% return all VSCs that mention any variable in that set:
% \begin{code}
% -- NOT USED ANYWHERE!
% citingASCs :: VarSet -> SideCond -> [VarSideConds]
% citingASCs vs (sc,_) = filter (cited vs) sc
%
% cited :: VarSet -> VarSideConds -> Bool
% vs `cited` vsc  =  vs == vscVSet vsc
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
     [tst_scChkDisjoint, tst_scChkCovers ]


tstFalse = Nothing
tstTrue  = Just Nothing
tstWhatever sc = Just $ Just sc

ils  = jId "ls" 
vls = Vbl ils ObsV Before
vls' = Vbl ils ObsV After
vls1 = Vbl ils ObsV $ During "1"
lexpr_t = GivenType $ jId "LE"
ls_t = TypeCons (jId "P") [lexpr_t]
o = jId "O"  
vO  = PreVar o 
lO  = LVbl vO [] []  ; gO  = LstVar lO
vO' = PostVar o ; lO' = LVbl vO' [] [] ; gO' = LstVar lO'


vE = ExprVar (jId "E") Static ; tE = jVar ls_t vE ; gE = StdVar vE
vN = ExprVar (jId "N") Static ; tN = jVar ls_t vN ; gN = StdVar vN
vR = ExprVar (jId "R") Static ; tR = jVar ls_t vR
va = Vbl (jId "a") PredV Static 
a = fromJust $ pVar ArbType va ; ga = StdVar va
tls = jVar ls_t vls
tls' = jVar ls_t vls'
eNotObs = [gO,gO'] `notin` gE
nNotObs = [gO,gO'] `notin` gN
eNO = [gE] `notin` gO  -- but this is really gE notin fv(gO), gO is listvar
nNO = [gN] `notin` gO  -- but this is really gN notin fv(gO), gO is listvar

tst_scChkDisjoint
 = testGroup "disjfrom  (no known vars)"
    [ testCase "Definitely True: ls   `disj` ls'"
       ( mkVSC (StdVar vls) (nsngl $ StdVar vls') NA NA 
         @?= Just Nothing )
    , testCase "Definitely True: ls_1 `disj` ls"
       ( mkVSC (StdVar vls1) (nsngl $ StdVar vls) NA NA 
         @?= Just Nothing )
    , testCase "gv_a `disjoint` empty is True"
       ( vscCheck (disjfrom  gv_a S.empty) @?= tstTrue )
    , testCase "v_e `disjoint` empty is True"
       ( vscCheck (disjfrom  v_e S.empty) @?= tstTrue )
    , testCase "gv_a `disjoint` {gv_a} is False"
       ( vscCheck (disjfrom  gv_a $ S.singleton gv_a) @?= tstFalse )
    , testCase "gv_a `disjoint` {gv_b} is True"
       ( vscCheck (disjfrom  gv_a $ S.singleton gv_b) @?= tstTrue )
    , testCase "v_e `disjoint` {v_e} stands"
       ( vscCheck (disjfrom  v_e $ S.singleton v_e)
         @?= tstWhatever  (disjfrom  v_e $ S.singleton v_e) )
    , testCase "v_e `disjoint` {v_f} stands"
       ( vscCheck (disjfrom  v_e $ S.singleton v_f)
         @?= tstWhatever  (disjfrom  v_e $ S.singleton v_f) )
    , testCase "v_e `disjoint` {gv_a} stands"
       ( vscCheck (disjfrom  v_e $ S.singleton gv_a)
         @?= tstWhatever  (disjfrom  v_e $ S.singleton gv_a) )
    , testCase "gv_a `disjoint` {v_f} stands"
       ( vscCheck (disjfrom  gv_a $ S.singleton v_f)
         @?= tstWhatever  (disjfrom  gv_a $ S.singleton v_f) )
    , testCase "gv_a `disjoint` {gv_b,v_f} stands without gv_b"
       ( vscCheck (disjfrom  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (disjfrom  gv_a $ S.fromList [v_f]) )
    ]

tst_scChkCovers
 = testGroup "coveredby  (no known vars)"
    [ testCase "gv_a `coveredby` empty is False"
       ( vscCheck (coveredby  gv_a S.empty) @?= tstFalse )
    , testCase "v_e `coveredby` empty stands"
       ( vscCheck (coveredby  v_e S.empty)
         @?= tstWhatever (coveredby  v_e S.empty) )
    , testCase "gv_a `coveredby` {gv_a} is True"
       ( vscCheck (coveredby  gv_a $ S.singleton gv_a) @?= tstTrue )
    , testCase "gv_a `coveredby` {gv_b} is False"
       ( vscCheck (coveredby  gv_a $ S.singleton gv_b) @?= tstFalse )
    , testCase "v_e `coveredby` {v_e} is True"
       ( vscCheck (coveredby  v_e $ S.singleton v_e) @?= tstTrue )
    , testCase "v_e `coveredby` {v_f} stands"
       ( vscCheck (coveredby  v_e $ S.singleton v_f)
         @?= tstWhatever  (coveredby  v_e $ S.singleton v_f) )
    , testCase "v_e `coveredby` {gv_a} stands"
       ( vscCheck (coveredby  v_e $ S.singleton gv_a)
         @?= tstWhatever  (coveredby  v_e $ S.singleton gv_a) )
    , testCase "gv_a `coveredby` {v_f} stands"
       ( vscCheck (coveredby  gv_a $ S.singleton v_f)
         @?= tstWhatever  (coveredby  gv_a $ S.singleton v_f) )
    , testCase "gv_a `coveredby` {gv_b,v_f} stands"
       ( vscCheck (coveredby  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (coveredby  gv_a $ S.fromList [v_f]) )
    ]
\end{code}

\subsection{Merging Tests}

\begin{code}
tst_mrgAtmCond :: TF.Test
tst_mrgAtmCond
 = testGroup "Merging Side-Conditions (no known vars)"
     [ testCase "merge gv_a `disjoint` empty  into [] is True"
        ( mrgVarConds (disjfrom  gv_a S.empty) [] @?= Just [] )
     , testCase "merge gv_a `disjoint` {gv_a} into [] is False"
        ( mrgVarConds (disjfrom  gv_a $ S.singleton gv_a) [] @?= Nothing )
     , testCase "merge v_e `coveredby` {v_f}  into [] is [itself]"
        ( mrgVarConds (coveredby  v_e $ S.singleton v_f) []
          @?= Just [coveredby  v_e $ S.singleton v_f] )
     , testCase "merge gv_a `disjoint` empty  into [vsc(gv_b)] is [vsc(gv_b)]"
        ( mrgVarConds (disjfrom  gv_a S.empty) [vsc1] @?= Just [vsc1] )
     , testCase "merge gv_a `disjoint` {gv_a} into [vsc(gv_b)] is False"
        ( mrgVarConds (disjfrom  gv_a $ S.singleton gv_a) [vsc1] @?= Nothing )
     , testCase
        "merge v_e `coveredby` {v_f}  into [vsc(gv_b)] is [vsc(gv_b),itself]"
        ( mrgVarConds (coveredby  v_e $ S.singleton v_f) [vsc1]
          @?= Just [vsc1,coveredby  v_e $ S.singleton v_f] )
     ]

vsc1 = (coveredby  gv_b $ S.fromList [gv_b,v_f])
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
  = testGroup "disjfrom  discharges ..."
      [ testCase "1+1=2" ( 1+1 @?= 2)
      ]
\end{code}


\subsection{Exported Test Group}

\begin{code}
int_tst_SideCond :: [TF.Test]
int_tst_SideCond
  = [ testGroup "\nSideCond Internal"
       [ 
         tst_scCheck
       , tst_mrgAtmCond
       , tst_ascDischarge
       ]
    ]
\end{code}
