\chapter{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  UVarSet, uset
, VarSideConds(..)
, termVar, disjointFrom, coveredBy, coveredDynamic
, mkVSC
, vscTrue, disjTrue, covByTrue
, vscVSet
, disjfrom, coveredby, dyncovered, ucoveredby, udyncovered
, allPreObs, allPostObs, allDynObs
, SideCond, scTrue, isTrivialSC
, onlyFreshSC -- , onlyInvolving, onlyFreshOrInvolved
-- , scGVars
, scVarSet
, mrgVarConds, mrgSideCond, mrgSideConds, mkSideCond
, scDischarge
, isFloatingVSC
, notin, covers, dyncover, fresh
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
The coverage conditions are true if $C$ or $C_d$ cover all possible variables, which we can capture with the idea of a universe set $U$ or $U_d$.
So we can represent the true side-condition for any $T$ by:
$$
  \emptyset \disj T \land 
  U \supseteq T 
  \land U_d \supseteq_a T
$$
This compresses to $(T,\emptyset,U,U_d)$.
We use $\texttt{Just } C$ to represent general $C$,
and $\texttt{Nothing}$ to represent $U$
(and similarly for $C_d$).
\begin{code}
type UVarSet = Maybe VarSet
uset :: UVarSet -> VarSet
uset Nothing    =  S.singleton (StdVar $ StaticVar $ jId "UNIVERSE")
uset (Just vs)  =  vs 

-- lift regular set operarions to UVarSet, where Nothing is the universal set
udiff :: UVarSet -> UVarSet -> UVarSet
udiff _        Nothing   =  Just S.empty
udiff Nothing  _         =  Nothing -- approximation
udiff (Just s) (Just t)  =  Just (s `S.difference` t)

uunion :: UVarSet -> UVarSet -> UVarSet
uunion _        Nothing   =  Nothing
uunion Nothing  _         =  Nothing
uunion (Just s) (Just t)  =  Just (s `S.union` t)

uintsct :: UVarSet -> UVarSet -> UVarSet
uintsct uset1    Nothing   =  uset1
uintsct Nothing  uset2     =  uset2
uintsct (Just s) (Just t)  =  Just (s `S.intersection` t)

unull :: UVarSet -> Bool
unull Nothing = False
unull (Just s)  = S.null s

usubset :: UVarSet -> UVarSet -> Bool
usubset _        Nothing   =  True
usubset Nothing  _         =  False
usubset (Just s) (Just t)  =  s `S.isSubsetOf` t

udisj :: UVarSet -> UVarSet -> Bool
udisj uset1    Nothing   =  unull uset1
udisj Nothing  uset2     =  unull uset2
udisj (Just s) (Just t)  =  S.null (s `S.intersection` t)
\end{code}

\newpage
\section{Variable Side-Conditions}

We now introduce our notion of term-variable side-conditions.
We will not represent $pre$ explicitly here,
and instead will use $\lst O \supseteq T$.

\begin{code}
data  VarSideConds -- (T,D,C,C_d)
  = VSC  GenVar        --  T,l$
          VarSet        --  D
          UVarSet  --  U  | C
          UVarSet  --  Ud | Cd
  deriving (Eq, Ord, Show, Read)

termVar        :: VarSideConds -> GenVar
termVar (VSC gv vsD uvsC uvsCd)         =  gv
disjointFrom   :: VarSideConds -> VarSet
disjointFrom (VSC gv vsD uvsC uvsCd)    =  vsD
coveredBy      :: VarSideConds -> UVarSet
coveredBy (VSC gv vsD uvsC uvsCd)       =  uvsC
coveredDynamic :: VarSideConds -> UVarSet
coveredDynamic (VSC gv vsD uvsC uvsCd)  =  uvsCd

disjTrue = S.empty
covByTrue = Nothing
vscTrue gv = VSC gv disjTrue covByTrue covByTrue
\end{code}

We need a smart builder here to handle all being true:
\begin{code}
mkVSC :: GenVar -> VarSet -> UVarSet -> UVarSet -> Maybe VarSideConds
mkVSC gv vsD uvsC uvsCd
  = if vsD == disjTrue && uvsC == covByTrue && uvsCd == covByTrue
    then Nothing -- denotes True
    else Just $ VSC gv vsD uvsC uvsCd
\end{code}


Collecting all sets explicitly mentioned:
\begin{code}
vscVSet :: VarSideConds -> VarSet
vscVSet vsc  
  =  disjointFrom vsc 
     `S.union` 
     (asSet $ coveredBy vsc) 
     `S.union` 
     (asSet $ coveredDynamic vsc)
  where 
   asSet Nothing    =  S.empty
   asSet (Just vs)  =  vs
\end{code}

We provide some builders when only one of the three conditions is involved:
\begin{code}
disjfrom, coveredby, dyncovered :: GenVar -> VarSet -> VarSideConds
gv `disjfrom`   vs  =  VSC gv vs       covByTrue covByTrue
gv `coveredby`  vs  =  VSC gv disjTrue (Just vs) covByTrue
gv `dyncovered` vs  =  VSC gv disjTrue covByTrue (Just vs)
ucoveredby, udyncovered :: GenVar -> UVarSet -> VarSideConds
gv `ucoveredby`  Nothing    =  vscTrue gv
gv `ucoveredby`  (Just vs)  =  gv `coveredby`  vs
gv `udyncovered` Nothing    =  vscTrue gv
gv `udyncovered` (Just vs)  =  gv `dyncovered` vs
\end{code}

\newpage
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
vscCheck :: MonadFail m => VarSet -> VarSideConds 
          -> m (Maybe VarSideConds)
vscCheck obsv (VSC gv vsD uvsC uvsCd)
  = do  vsD'   <- disjointCheck  obsv gv vsD
        uvsC'  <- coveredByCheck obsv gv uvsC
        uvsCd' <- dynCvrgCheck   obsv gv uvsCd
        return $ mkVSC gv vsD' uvsC' uvsCd'
\end{code}

The key trick is to take \m{g ~R~ \setof{g_1,\dots,g_n}}
and break it down into individual comparisons (\m{g ~R~ \setof{g_i}}).


\subsubsection{Checking Disjoint $ V \disj g$}

Here, \m{g \disj \setof{g_1,\dots,g_n}}
reduces to \m{\bigwedge_{i \in 1\dots n}(g \disj \setof{g_i})}.

\begin{code}
disjointCheck  :: MonadFail m 
               => VarSet -> GenVar -> VarSet -> m VarSet
disjointCheck obs gv vsD
  = disjCheck obs gv S.empty $ S.toList vsD


disjCheck :: MonadFail m
        => VarSet -> GenVar -> VarSet -> [GenVar] -> m VarSet
disjCheck obs gv vsd [] = return vsd
disjCheck obs gv vsd (gvd:gvs) = do
  vsd' <- disjChk obs gvd $ sort [gv,gvd]
  disjCheck obs gv (vsd `S.union` vsd') gvs

disjChk obs gvd [gv1,gv2] = return $ S.singleton gvd -- for now
\end{code}

\newpage
\subsubsection{Checking CoveredBy $V \supseteq g$}

\begin{eqnarray*}
   \emptyset             \supseteq z           && \false
\\ \dots,g,\dots{}       \supseteq g           && \true
\\ \{stdObs\}\setminus z \supseteq z           && \false
\\ \lst\ell\setminus Z \supseteq \lst\ell\setminus (Z\cup W) 
     && \true
\end{eqnarray*}

Here, as $T$ could be empty,
we cannot deduce that $\emptyset \supseteq T$ is false.
Similarly, $T \supseteq z$ could also be true.
\begin{code}
coveredByCheck  :: MonadFail m 
               => VarSet -> GenVar -> UVarSet -> m (UVarSet)

coveredByCheck obsv gv Nothing  =  return covByTrue  -- U
coveredByCheck obsv gv jvsC@(Just vsC)
  | any (gvCovBy gv) vsC      =  return covByTrue
  | not $ isObsGVar gv        =  return jvsC
  | S.null vsC                =  report "tvar cover fails (null)"
  | all isStdV vsC            =  report "tvat cover fails (all std)"
  where 
    showsv = "gv = "++show gv
    showvs = "vsC = "++show vsC
    report msg = fail $ unlines' [msg,showsv,showvs]
coveredByCheck _ _ uvsC = return uvsC
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
\subsubsection{Checking DynamicCoverage $V \supseteq_a g$}

We start by defining the standard way 
to refer to all pre- and post-observations:
\begin{code}
o = jId "O"  ;  vO = PreVar o
allPreObs, allPostObs :: ListVar
allPreObs = PreVars o  ;  allPostObs = PostVars o 
allDynObs :: VarSet
allDynObs = S.fromList $ map LstVar [allPreObs,allPostObs]
\end{code}
We expect most uses of dynamic coverage to have the form $O,O' \supseteq_a V$.
Here $V$ may contain $O$ and $O'$, 
where $O$ ($O'$) is defined to be the set $ObsV$ ($ObsV'$) of actual observables, if any.
The \texttt{obsv} variable-set argument contains $ObsV \cup ObsV'$.

We first check that $V$ is only dynamic:
\begin{eqnarray*}
   \exists v \in V \bullet \lnot\isdyn(v) && \false
\end{eqnarray*}
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
dynCvrgCheck  :: MonadFail m 
               => VarSet -> GenVar -> UVarSet -> m (UVarSet)

dynCvrgCheck obsv gv Nothing  =  return covByTrue  -- U
dynCvrgCheck obsv gv jvsCd@(Just vsCd)
  | vsCd == allDynObs && gv `S.member` (obsv `S.union` allDynObs)
                            =  return covByTrue
  | hasStatic               =  report "tvar dyncover fails (static)"
  | any (gvCovBy gv) vsCd   =  return covByTrue
  | not $ isObsGVar gv      =  return jvsCd
  | S.null vsCd 
      =  if isDynGVar gv
         then report "atomic dyncover fails (null)"
         else return jvsCd
  | all isStdV vsCd         =  report "tvar dyncover fails (all std)"
  where 
    hasStatic = any (not . isDynGVar) vsCd
    showsv = "gv = "++show gv
    showvs = "vsCd = "++show vsCd
    report msg = fail $ unlines' [msg,showsv,showvs]
dynCvrgCheck _ _ uvsCd  =  return uvsCd
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
            => VarSet -> VarSideConds -> [VarSideConds] -> m [VarSideConds]
\end{code}
\textbf{Invariant}\\
For \texttt{mrgVarConds obs vsc vscs} we have:\\
\texttt{vscs} is ordered, and\\
for all \texttt{vsc'} in \texttt{vscs}\\
that \texttt{vscCheck obsv vsc' == Just vsc'}.


We start by checking the new VCS:
\begin{code}
mrgVarConds obsv vsc vscs
  = do masc <- vscCheck obsv vsc
       case masc of
         Nothing    ->  return vscs -- vsc is in fact true
         Just vsc'  ->  mrgVSC obsv vsc' vscs
\end{code}

Now we search to see if there is a VSCs with the
same general-variable, respecting the ordering:
\begin{code}
mrgVSC :: MonadFail m 
       => VarSet -> VarSideConds -> [VarSideConds] -> m [VarSideConds]

mrgVSC obsv vsc' []  = return [vsc']

mrgVSC obsv vsc' vscs@(vsc1:vscs')
  | v' < v1  =  return (vsc':vscs)
  | v' > v1  =  do vscs'' <- mrgVSC obsv vsc' vscs'
                   return ( vsc1 : vscs'' )
  | otherwise -- v' == v1
    = do  case mrgSameGVSC obsv vsc' vsc1 of
            Nothing            -> fail "mgrTVarConds: false s.c."
            Just Nothing       -> return vscs' -- mrg is true 
            Just (Just vsc'') -> return (vsc'':vscs')
  where
    v' = termVar vsc'
    v1 = termVar vsc1
\end{code}

\subsection{Merging two (checked) VSCs}

Now, merging an VSC in with another VSC referring to the same general variable:
\begin{code}
mrgSameGVSC :: MonadFail m => VarSet
           -> VarSideConds -> VarSideConds -> m (Maybe VarSideConds)
mrgSameGVSC obsv (VSC gv vsD1 uvsC1 uvsCd1) (VSC _ vsD2 uvsC2 uvsCd2) 
  = let 
      vsD'   =  vsD1   `S.union` vsD2
      uvsC'  =  uvsC1  `uintsct` uvsC2
      uvsCd' =  uvsCd1 `uintsct` uvsCd2
    in vscCheck obsv (VSC gv vsD' uvsC' uvsCd')
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
  \item[UTPBase]~\\
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
mrgTVarCondLists :: MonadFail m => VarSet
                -> [VarSideConds] -> [VarSideConds] -> m [VarSideConds]
mrgTVarCondLists obsv vscs1 [] = return vscs1
mrgTVarCondLists obsv vscs1 (VSC _ vsD Nothing Nothing:vscs2)
  | S.null vsD  =  mrgTVarCondLists obsv vscs1 vscs2
mrgTVarCondLists obsv vscs1 (vsc:vscs2)
     = do vscs1' <- mrgVarConds obsv vsc vscs1
          mrgTVarCondLists obsv vscs1' vscs2
\end{code}

\subsection{Merging Term Variable and Freshness Side-Conditions}


\begin{code}
mrgTVarFreshConditions :: MonadFail m 
                       => VarSet -> VarSet -> [VarSideConds] 
                       -> m SideCond
mrgTVarFreshConditions obsv freshvs vscs
  | freshvs `disjoint` coveredVarsOf obsv vscs  =  return (vscs,freshvs)
  -- the above might not work - `disjoint` may need more information
  | otherwise  =  fail "Fresh variables cannot cover terms."

coveredVarsOf :: VarSet -> [VarSideConds] -> VarSet
coveredVarsOf obsv vscs = S.unions $ map coveringsOf vscs
coveringsOf (VSC _ _ uvsC uvsCd)  =  cvr uvsC `S.union` cvr uvsCd
cvr Nothing    =  S.empty -- universe does not contain fresh vars
cvr (Just vs)  =  vs
\end{code}

\section{From VSC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: MonadFail m 
           => VarSet -> [VarSideConds] -> VarSet -> m SideCond
mkSideCond obsv vscs fvs
 = do vscs' <-  mrgTVarCondLists obsv [] vscs
      mrgTVarFreshConditions obsv fvs vscs'
\end{code}


\subsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each VSC and fresh set from the one into the other,
one at a time.
\begin{code}
mrgSideCond :: MonadFail m 
            => VarSet -> SideCond -> SideCond -> m SideCond
mrgSideCond obsv (vscs1,fvs1) (vscs2,fvs2)
     = do vscs' <- mrgTVarCondLists obsv vscs1 vscs2
          mrgTVarFreshConditions obsv (fvs1 `S.union` fvs2) vscs'
          -- the above may require a obsv-savvy union?

mrgSideConds :: MonadFail m => VarSet -> [SideCond] -> m SideCond
mrgSideConds obsv [] = return ([],S.empty)
mrgSideConds obsv (sc:scs)
  = do  scs' <- mrgSideConds obsv scs
        mrgSideCond obsv sc scs'

\end{code}

\subsection{Side-Condition Operators}

We want some shorthands for assembling side-conditions,
that are also ``total'',
in that they return \texttt{SideCond} rather than \texttt{m SideCond}.
\begin{code}
(.:) :: SideCond -> SideCond -> SideCond
sc1 .: sc2 = fromJust $ mrgSideCond S.empty sc1 sc2
mrgscs :: [SideCond] -> SideCond
mrgscs = fromJust . mrgSideConds S.empty
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
We first use those to simplfiy the consqequence.

\begin{code}
scDischarge obsv anteSC@(anteVSC,anteFvs) cnsqSC@(cnsqVSC,cnsqFvs)
  = do cnsqVSC' <- vscMrg obsv $ map (knownObsDischarge obsv) cnsqVSC
       let cnsqSC' = (cnsqVSC',cnsqFvs)
       if isTrivialSC cnsqSC' then return scTrue
       else if isTrivialSC anteSC then return cnsqSC'
       else do vsc' <- scDischarge' obsv anteVSC cnsqVSC'
               freshDischarge obsv anteFvs cnsqFvs vsc'
    
vscMrg obs [] = return []
vscMrg obs (vsc:vscs) = mrgVarConds obs vsc vscs    
\end{code}



\subsection{Known Observable  Discharge}

\begin{code}
knownObsDischarge :: VarSet -> VarSideConds -> VarSideConds
knownObsDischarge obs ( VSC gv vsD uvsC uvsCd )
                    =   VSC gv vsD uvsC (obsDischarge obs gv uvsCd)
\end{code}
Discharging dynamic coverage  ($Cd \supseteq_a V$).
Here $V \notin Cd$ or else this would have collapsed to $\true$ earlier.
We check if it is in $obs$, which is the expansion of $Cd$.
\begin{code}
obsDischarge :: VarSet -> GenVar -> UVarSet -> UVarSet
obsDischarge obsv gv uvsCd
  | gv `S.member` obsv  =  Nothing
  | otherwise           =  uvsCd
\end{code}



\subsection{Term-Variable  Condition  Discharge}

Now onto processing those ordered Term-Variable Side-Conditions:
\begin{code}
scDischarge'  :: MonadFail m => VarSet
              -> [VarSideConds] -> [VarSideConds]
              -> m [VarSideConds]
scDischarge' _ _ []      =  return []     --  discharged
scDischarge' _ [] vscL  =  return vscL  --  not discharged
scDischarge' obsv        (vscG@(VSC gvG _ _ _):restG) 
                  vscLs@(vscL@(VSC gvL _ _ _):restL)
  | gvG < gvL  =  scDischarge' obsv restG vscLs -- vscG not needed
  | gvG > gvL  =  do -- nothing available to discharge vscL
                     rest' <- scDischarge' obsv restG restL
                     return (vscL:rest')
  | otherwise  =  do -- use vscG to discharge vscL
                     vsc' <- vscDischarge obsv vscG vscL
                     vscChecked <- vscCheck obsv vsc'
                     case vscChecked of
                       Nothing ->  scDischarge' obsv restG restL
                       Just vsc'' -> do
                         rest' <- scDischarge' obsv restG restL
                         return (vsc'':rest')
\end{code}

\newpage


At this point we have the form, for given term-variable $T$:
\begin{equation}
 \left( D_G \disj T \land C_G \supseteq T \land Cd_G \supseteq_a T \right)
 \vdash
 \left( D_L \disj T \land C_L \supseteq T \land Cd_L \supseteq_a T \right)
\end{equation}
Finally, we have arrived at where the real work is done.

\begin{code}
vscDischarge :: MonadFail m => VarSet
              -> VarSideConds -> VarSideConds -> m VarSideConds
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
vscDischarge _ _ (VSC (StdVar (Vbl _ ObsV _)) dL _ _)
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
\\&=& O_m \disj (O \cup O')\mbox{, set theory}
\\ && \true
\\
O \cup O' \supseteq V &\discharges& O_m \disj V \text{, for any }m
\end{eqnarray*}
This is subsumed by the
$C_G \supseteq V \discharges D_L \disj V $
discharge rule further below.

\begin{code}
vscDischarge obsv (VSC gv vsDG uvsCG uvsCdG) (VSC _ vsDL uvsCL uvsCdL)
  = do  vsD'    <- ddDischarge obsv vsDG   vsDL
        vsD''   <- cdDischarge obsv uvsCG  vsD'
        vsD'''  <- cdDischarge obsv uvsCdG vsD''

        uvsC'   <- ccDischarge obsv uvsCG  uvsCL
        uvsC''  <- dcDischarge obsv vsDG   uvsC'

        uvsCd'  <- ccDischarge obsv uvsCdG uvsCdL
        uvsCd'' <- dcDischarge obsv vsDG   uvsCd'

        return $ VSC gv vsD''' uvsC'' (obsDischarge obsv gv uvsCd'')
\end{code}

\newpage
\subsubsection{Pairwise Discharging}

\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true
         \quad\cond{D_L \subseteq D_G}\quad (D_L\setminus D_G) \disj V
\end{eqnarray*}
\begin{code}
ddDischarge :: MonadFail m => VarSet -> VarSet -> VarSet -> m VarSet
ddDischarge obsv vsDG vsDL = return (vsDL `S.difference` vsDG)
\end{code}

\begin{eqnarray*}
   \_ \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad V \in Obs \land C_L = Obs
\\ C_G \supseteq V \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad C_G \subseteq C_L
\\ & = & \false, \quad \IF \quad C_G \disj C_L \land isStdObs(V)
\\ & = & (C_G \cap C_L)\cup C_{?L} \supseteq V, \quad \textbf{otherwise}
\end{eqnarray*}
Remember, here \texttt{Nothing} denotes the universal set.
\begin{code}
ccDischarge :: MonadFail m 
            => VarSet -> UVarSet -> UVarSet 
            -> m UVarSet
ccDischarge obsv uvsCG uvsCL
  | uvsCG `usubset` uvsCL  =  return Nothing
  | otherwise              =  return ((uvsCG `uintsct` uvsCL) `uunion` uvsCLf)
  where uvsCLf = case uvsCL of
                   Nothing    ->  Nothing
                   Just vsCL  ->  Just $ S.filter isFloatingGVar vsCL
\end{code}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false
         \quad\cond{C_L \subseteq D_G \land isStdObs(V)}\quad
         (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
\begin{code}
dcDischarge :: MonadFail m => VarSet -> VarSet -> UVarSet -> m UVarSet
dcDischarge obsv _    Nothing      =  return Nothing
dcDischarge obsv vsDG (Just vsCL)  =  return $ Just (vsCL `S.difference` vsDG)
\end{code}

\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & = & \true
         \quad\cond{C_G\cap D_L = \emptyset}\quad
         D_L \disj V
\end{eqnarray*}
\begin{code}
cdDischarge :: MonadFail m => VarSet -> UVarSet -> VarSet -> m VarSet
cdDischarge obsv Nothing vsDL      =  return vsDL
cdDischarge obsv (Just vsCG) vsDL  =  return (vsCG `S.intersection` vsDL) 
\end{code}



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
freshTVarDischarge obsv gF (VSC gv vsD uvsC uvsCd)
  | vsc' == vscTrue gv  =  return []
  | otherwise  =  return [vsc']
  where
    uvsgF = Just gF
    vsD' = vsD `S.difference` gF
    uvsC' = uvsC `udiff` uvsgF
    uvsCd' = if gv `S.member` obsv
             then uvsCd `udiff` uvsgF
             else Nothing
    vsc' = VSC gv vsD' uvsC' uvsCd'
\end{code}

\newpage
\section{Check for Floating Conditions}

When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check that \emph{all} the term variable side-conditions in that residual
mention variables that are marked as ``floating''.
Only these can possibly be instantiated to satisfy the residual side-condition.
\begin{code}
isFloatingVSC :: VarSideConds -> Bool
isFloatingVSC (VSC  gv vsD uvsC uvsCd)
  = isFloatingGVar gv || 
    ( hasFloating vsD && hasFloatingM uvsC && hasFloatingM uvsCd )
hasFloating :: VarSet -> Bool
hasFloating vs = any isFloatingGVar $ S.toList vs
hasFloatingM :: UVarSet -> Bool
hasFloatingM Nothing = False
hasFloatingM (Just vs) = hasFloating vs
\end{code}
% One exception to this, during law matching,
% is that coverage may reduce to the empty set
% because unbound variables given a temporary binding
% to a ``?'' variable (\texttt{bindFloating})
% will not cancel out other variables that they should be able to do,
% if instantiated properly.
% \begin{code}
% tolerateAutoOrNull :: VarSet -> VarSideConds -> Bool
% tolerateAutoOrNull unbound (VSC _ vsD uvsC uvsCd) 
% =  unbound `overlaps` vsD
% tolerateAutoOrNull unbound (CoveredBy _  _ c)   =  S.null c || unbound `overlaps` c
% tolerateAutoOrNull _       _              =  False
% autoOrNullInAll unbound = all (tolerateAutoOrNull unbound)
% \end{code}



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
findGenVar :: MonadFail m => GenVar -> SideCond -> m VarSideConds
findGenVar gv ( vscs, _ )  =  findGV gv vscs

findGV _ [] = fail "findGenVar: not in any term variable side-condition"
findGV gv (vsc:vscs)
  | gv `mentionedBy` vsc  =  return vsc
  | otherwise             =  findGV gv vscs

mentionedBy :: GenVar -> VarSideConds -> Bool
gv `mentionedBy` vsc
  | otherwise      =  gv == termVar vsc
\end{code}

We then look at returning all mentions of a variable:
\begin{code}
findAllGenVar :: GenVar -> SideCond -> [VarSideConds]
findAllGenVar gv ( vscs, _ )  =  findAGV gv [] vscs

findAGV _ scsa []  =  reverse scsa
findAGV gv scsa (vsc:vscs)
  | gv `mentionedBy` vsc  =  findAGV gv (vsc:scsa) vscs
  | otherwise             =  findAGV gv scsa       vscs
\end{code}

We sometimes want mentions for a specific condition type:
\begin{code}
findCoveredGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findCoveredGenVar gv ( vscs, _ ) = findCGV gv vscs

findCGV gv []         =  fail ("Covered "++show gv ++ " not found")
findCGV gv ((VSC gv' _ (Just vs) _):vscs)
  | gv == gv'         =  return vs
findCGV gv (_:vscs)  =  findCGV gv vscs
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
lexpr_t = GivenType $ jId "LE"
ls_t = TypeCons (jId "P") [lexpr_t]
-- o = jId "O"  
-- vO  = PreVar o 
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
    [ testCase "gv_a `disjoint` empty is True"
       ( vscCheck S.empty (disjfrom  gv_a S.empty) @?= tstTrue )
    , testCase "v_e `disjoint` empty is True"
       ( vscCheck S.empty (disjfrom  v_e S.empty) @?= tstTrue )
    , testCase "gv_a `disjoint` {gv_a} is False"
       ( vscCheck S.empty (disjfrom  gv_a $ S.singleton gv_a) @?= tstFalse )
    , testCase "gv_a `disjoint` {gv_b} is True"
       ( vscCheck S.empty (disjfrom  gv_a $ S.singleton gv_b) @?= tstTrue )
    , testCase "v_e `disjoint` {v_e} stands"
       ( vscCheck S.empty (disjfrom  v_e $ S.singleton v_e)
         @?= tstWhatever  (disjfrom  v_e $ S.singleton v_e) )
    , testCase "v_e `disjoint` {v_f} stands"
       ( vscCheck S.empty (disjfrom  v_e $ S.singleton v_f)
         @?= tstWhatever  (disjfrom  v_e $ S.singleton v_f) )
    , testCase "v_e `disjoint` {gv_a} stands"
       ( vscCheck S.empty (disjfrom  v_e $ S.singleton gv_a)
         @?= tstWhatever  (disjfrom  v_e $ S.singleton gv_a) )
    , testCase "gv_a `disjoint` {v_f} stands"
       ( vscCheck S.empty (disjfrom  gv_a $ S.singleton v_f)
         @?= tstWhatever  (disjfrom  gv_a $ S.singleton v_f) )
    , testCase "gv_a `disjoint` {gv_b,v_f} stands"
       ( vscCheck S.empty (disjfrom  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (disjfrom  gv_a $ S.fromList [gv_b,v_f]) )
    ]

tst_scChkCovers
 = testGroup "coveredby  (no known vars)"
    [ testCase "gv_a `coveredby` empty is False"
       ( vscCheck S.empty (coveredby  gv_a S.empty) @?= tstFalse )
    , testCase "v_e `coveredby` empty stands"
       ( vscCheck S.empty (coveredby  v_e S.empty)
         @?= tstWhatever (coveredby  v_e S.empty) )
    , testCase "gv_a `coveredby` {gv_a} is True"
       ( vscCheck S.empty (coveredby  gv_a $ S.singleton gv_a) @?= tstTrue )
    , testCase "gv_a `coveredby` {gv_b} is False"
       ( vscCheck S.empty (coveredby  gv_a $ S.singleton gv_b) @?= tstFalse )
    , testCase "v_e `coveredby` {v_e} is True"
       ( vscCheck S.empty (coveredby  v_e $ S.singleton v_e) @?= tstTrue )
    , testCase "v_e `coveredby` {v_f} stands"
       ( vscCheck S.empty (coveredby  v_e $ S.singleton v_f)
         @?= tstWhatever  (coveredby  v_e $ S.singleton v_f) )
    , testCase "v_e `coveredby` {gv_a} stands"
       ( vscCheck S.empty (coveredby  v_e $ S.singleton gv_a)
         @?= tstWhatever  (coveredby  v_e $ S.singleton gv_a) )
    , testCase "gv_a `coveredby` {v_f} stands"
       ( vscCheck S.empty (coveredby  gv_a $ S.singleton v_f)
         @?= tstWhatever  (coveredby  gv_a $ S.singleton v_f) )
    , testCase "gv_a `coveredby` {gv_b,v_f} stands"
       ( vscCheck S.empty (coveredby  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (coveredby  gv_a $ S.fromList [gv_b,v_f]) )
    ]
\end{code}

\subsection{Merging Tests}

\begin{code}
tst_mrgAtmCond :: TF.Test
tst_mrgAtmCond
 = testGroup "Merging Side-Conditions (no known vars)"
     [ testCase "merge gv_a `disjoint` empty  into [] is True"
        ( mrgVarConds S.empty (disjfrom  gv_a S.empty) [] @?= Just [] )
     , testCase "merge gv_a `disjoint` {gv_a} into [] is False"
        ( mrgVarConds S.empty (disjfrom  gv_a $ S.singleton gv_a) [] @?= Nothing )
     , testCase "merge v_e `coveredby` {v_f}  into [] is [itself]"
        ( mrgVarConds S.empty (coveredby  v_e $ S.singleton v_f) []
          @?= Just [coveredby  v_e $ S.singleton v_f] )
     , testCase "merge gv_a `disjoint` empty  into [vsc(gv_b)] is [vsc(gv_b)]"
        ( mrgVarConds S.empty (disjfrom  gv_a S.empty) [vsc1] @?= Just [vsc1] )
     , testCase "merge gv_a `disjoint` {gv_a} into [vsc(gv_b)] is False"
        ( mrgVarConds S.empty (disjfrom  gv_a $ S.singleton gv_a) [vsc1] @?= Nothing )
     , testCase
        "merge v_e `coveredby` {v_f}  into [vsc(gv_b)] is [vsc(gv_b),itself]"
        ( mrgVarConds S.empty (coveredby  v_e $ S.singleton v_f) [vsc1]
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
