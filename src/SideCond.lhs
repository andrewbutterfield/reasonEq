\chapter{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  TVarSideConds, tvscTrue
, tvscVSet
, disjfrom, coveredby, dyncovered
, SideCond, scTrue, isTrivialSC
, onlyFreshSC -- , onlyInvolving, onlyFreshOrInvolved
-- , scGVars
, scVarSet
, mrgTVarConds, mrgSideCond, mrgSideConds, mkSideCond
, scDischarge
, isFloatingTVSC
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

\subsection{Term-Variable Side-Conditions}

An term variable side-condition (TVSC) can have one of the following forms,
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
So we can represent the true side-conition for any $T$ by:
$$
  \emptyset \disj T \land 
  U \supseteq T 
  \land U_d \supseteq_a T
$$
This compresses to $(T,\emptyset,U,U_d)$.

\section{Term Variable Side-Conditions}

We now introduce our notion of term-variable side-conditions.
We will not represent $pre$ explicitly here,
and instead will use $\lst O \supseteq T$.
We use $\texttt{Just } C$ to represent general $C$,
and $\texttt{Nothing}$ to represent $U$
(and similarly for $C_d$).
\begin{code}
data  TVarSideConds -- (T,D,C,C_d)
  = TVSC  { termVar         ::  GenVar        --  T
          , disjointFrom    ::  VarSet        --  D
          , coveredBy       ::  Maybe VarSet  --  U  | C
          , coveredDynamic  ::  Maybe VarSet  --  Ud | Cd
          }
disjTrue = S.empty
covByTrue = Nothing
tvscTrue t = TVSC t disjTrue covByTrue covByTrue
\end{code}

We need a smart builder here to handle all being true:
\begin{code}
mkTVSC :: GenVar -> VarSet -> Maybe VarSet -> Maybe VarSet -> Maybe TVarSideConds
mkTVSC gv vsD mvsC mvsCd
  = if vsD == disjTrue && mvsC == covByTrue && mvsCd == covByTrue
    then Nothing -- denotes True
    else Just $ TVSC gv vsD mvsC mvsCd
\end{code}


Selectors:
\begin{code}
tvscVSet :: TVarSideConds -> VarSet
tvscVSet tvsc  
  =  disjointFrom tvsc `S.union` coveredBy tvsc `S.union` coveredDynamic tvsc
\end{code}

We provide some builders when only one of the three conditions is involved:
\begin{code}
disjfrom, coveredby, dyncovered :: GenVar -> VarSet -> TVarSideConds
gv `disjfrom`   vs  =  TVSC gv vs       covByTrue covByTrue
gv `coveredby`  vs  =  TVSC gv disjTrue (Just vs) covByTrue
gv `dyncovered` vs  =  TVSC gv disjTrue covByTrue (Just vs) 
\end{code}


\subsection{Checking Atomic Sideconditions}

Here we provide a monadic function that fails if the condition
is demonstrably false,
and otherwise returns a \texttt{Maybe} type,
where \texttt{Nothing} denotes a condition that is true.

We need to do this in general
in the context of what is ``known'' about variables.
Here, $z$ denotes an (standard) observation variable,
$T$ denotes a standard term variable,
and $g$ denotes either $z$ or $T$.
We also use the case conventions described earlier ($P, p, p'$).

\begin{code}
mscTrue = Nothing
tvscCheck :: MonadFail m => [Subscript] -> TVarSideConds 
          -> m (Maybe TVarSideConds)
tvscCheck ss (TVSC gv vsD mvsC mvsCd)
  = do  vsD'   <- disjointCheck  ss gv vsD
        mvsC'  <- coveredByCheck ss gv mvsC
        mvsCd' <- dynCvrgCheck   ss gv mvsCd
        return $ mkTVSC gv vsD' mvsC' mvsCd'
\end{code}

\subsubsection%
{Checking Disjoint $ V \disj g$}

\begin{eqnarray*}
   \emptyset             \disj g           &&   \true
\\ \dots,z,\dots         \disj z           &&   \false
\\ \{stdObs\}\setminus z \disj z           &&   \true
\end{eqnarray*}

Note that we cannot deduce (here) that $T \disj T$ is false,
because $T$ could correspond to the empty set.
Nor can we assume $T \disj z$ is false, because $T$ could contain $z$.
\begin{code}
disjointCheck  :: MonadFail m 
               => [Subscript] -> GenVar -> VarSet -> m VarSet
disjointCheck ss gv vs
  | S.null vs                 =  return disjTrue
  | not $ isObsGVar gv        =  return vs
  | gv `S.member` vs          =  report "tvar disjoint fails"
  | all isStdV    vs          =  return disjTrue
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
\\ \lst\ell\setminus Z \supseteq \lst\ell\setminus (Z\cup W) 
     && \true
\end{eqnarray*}

Here, as $T$ could be empty,
we cannot deduce that $\emptyset \supseteq T$ is false.
Similarly, $T \supseteq z$ could also be true.
\begin{code}
coveredByCheck  :: MonadFail m 
               => [Subscript] -> GenVar -> Maybe VarSet -> m (Maybe VarSet)

coveredByCheck ss gv Nothing = return covByTrue  -- U
coveredByCheck ss gv jvs@(Just vs)
  | any (gvCovBy gv) vs  =  return covByTrue
  | not $ isObsGVar gv   =  return jvs
  | S.null vs            =  report "tvar cover fails (null)"
  | all isStdV vs        =  report "tvat cover fails (all std)"
  where 
    showsv = "gv = "++show gv
    showvs = "vs = "++show vs
    report msg = fail $ unlines' [msg,showsv,showvs]
\end{code}

\newpage
\subsubsection{Checking DynamicCoverage $V \supseteq_a g$}

We first check that $V$ is only dynamic:
\begin{eqnarray*}
   \exists v \in V \bullet \lnot\isdyn(v) && \false
\end{eqnarray*}
Assuming $\forall v \in V \bullet \isdyn(v)$ we then proceed:
\begin{eqnarray*}
   \emptyset             \supseteq_a z   &&  \lnot\isdyn(z)
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
               => [Subscript] -> GenVar -> Maybe VarSet -> m (Maybe VarSet)

dynCvrgCheck ss gv Nothing = return covByTrue  -- U
dynCvrgCheck ss gv jvs@(Just vs)
  | hasStatic            =  report "tvar dyncover fails (static)"
  | any (gvCovBy gv) vs  =  return covByTrue
  | not $ isObsGVar gv   =  return jvs
  | S.null vs 
      =  if isDynGVar gv
         then report "atomic dyncover fails (null)"
         else return jvs
  | all isStdV vs        =  report "tvar dyncover fails (all std)"
  where 
    hasStatic = any (not . isDynGVar) vs
    showsv = "gv = "++show gv
    showvs = "vs = "++show vs
    report msg = fail $ unlines' [msg,showsv,showvs]
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

A ``full'' side-condition is basically 
a list of term-variable side-conditions,
interpreted as their conjunction,
along with a set defining fresh variables.
\begin{code}
type SideCond = ( [TVarSideConds]  -- all must be true
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
onlyFreshSC (tvscs,_) = null tvscs
\end{code}
Finally,
sometimes we want all the variable-sets
from a side-condition:
\begin{code}
scVarSet :: SideCond -> VarSet
scVarSet (tvscs,fvs) = (S.unions $ map tvscVSet tvscs) `S.union` fvs
\end{code}

\section{Merging Side-Conditions}

The list of TVSCs
is kept ordered by the \texttt{GenVar} component,
and any given such variable occurs at most once.


The function \texttt{mrgTVarConds} below is the ``approved'' way
to generate side-conditions,
by merging them in, one at a time,
into a pre-existing list ordered and structured as described above.

\begin{code}
mrgTVarConds :: MonadFail m => [Subscript]
           -> TVarSideConds -> [TVarSideConds] -> m [TVarSideConds]
\end{code}

1st TVSC is easy:
\begin{code}
mrgTVarConds ss tvsc []
  = do masc <- tvscCheck ss tvsc
       case masc of
         Nothing ->  return [] -- tvsc is in fact true
         Just tvsc' -> return [tvsc']
\end{code}

Subsequent ones mean searching to see if there are already TVSCs with the
same general-variable:
\begin{code}
mrgTVarConds ss tvsc (tvsc1:tvscs)
  | termVar tvsc == termVar tvsc1
    = do  masc <- tvscCheck ss tvsc
          case masc of
            Nothing
              ->  return tvscs
            Just tvsc'
              ->  case mrgTVarTVar ss tvsc' tvsc1 of
                    Nothing            -> fail "mgrTVarConds: false s.c."
                    Just Nothing       -> return tvscs -- mrg is true 
                    Just (Just tvsc'') -> return (tvsc'':tvscs)
  | otherwise 
    = do  tvscs' <- mrgTVarConds ss tvsc1 tvscs
          return (tvsc:tvscs')
\end{code}

\subsection{Merging one TVSC with relevant others}

Now, merging an TVSC in with another TVSC referring to the same general variable:
\begin{code}
mrgTVarTVar :: MonadFail m => [Subscript]
           -> TVarSideConds -> TVarSideConds -> m (Maybe TVarSideConds)
mrgTVarTVar ss (TVSC gv vsD1 mvsC1 mvsCd1) (TVSC _ vsD2 mvsC2 mvsCd2) 
  = let 
      vsD'   =  vsD1    `S.union`   vsD2
      mvsC'  =  mvsC1  `mintersect` mvsC2
      mvsCd' =  mvsCd1 `mintersect` mvsCd2
    in tvscCheck ss (TVSC gv vsD' mvsC' mvsCd')

-- Nothing here denotes the relevant universal set - unit for intersection
Nothing  `mintersect` mvs       =  mvs
mvs      `mintersect` Nothing   =  mvs
Just vs1 `mintersect` Just vs2  =  Just (vs1 `S.intersection` vs2)
\end{code}


\subsection{TVSC Merge Laws}

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

\begin{code}
mrgTVarCondLists :: MonadFail m => [Subscript]
                -> [TVarSideConds] -> [TVarSideConds] -> m [TVarSideConds]
mrgTVarCondLists ss tvscs1 [] = return tvscs1
mrgTVarCondLists ss tvscs1 (tvsc:tvscs2)
     = do tvscs1' <- mrgTVarConds ss tvsc tvscs1
          mrgTVarCondLists ss tvscs1' tvscs2
\end{code}

\subsection{Merging Term Variable and Freshness Side-Conditions}


\begin{code}
mrgTVarFreshConditions :: MonadFail m 
                       => [Subscript] -> VarSet -> [TVarSideConds] 
                       -> m SideCond
mrgTVarFreshConditions ss freshvs tvscs
  | freshvs `disjoint` coveredVarsOf ss tvscs  =  return (tvscs,freshvs)
  -- the above might not work - `disjoint` may need more information
  | otherwise  =  fail "Fresh variables cannot cover terms."

coveredVarsOf :: [Subscript] -> [TVarSideConds] -> VarSet
coveredVarsOf ss tvscs = S.unions $ map coveringsOf tvscs
coveringsOf (TVSC _ _ mvsC mvsCd)  =  cvr mvsC `S.union` cvr mvsCd
cvr Nothing    =  S.empty -- universe does not contain fresh vars
cvr (Just vs)  =  vs
\end{code}

\section{From TVSC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: MonadFail m 
           => [Subscript] -> [TVarSideConds] -> VarSet -> m SideCond
mkSideCond ss tvscs fvs
 = do tvscs' <-  mrgTVarCondLists ss [] tvscs
      mrgTVarFreshConditions ss fvs tvscs'
\end{code}


\subsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each TVSC and fresh set from the one into the other,
one at a time.
\begin{code}
mrgSideCond :: MonadFail m 
            => [Subscript] -> SideCond -> SideCond -> m SideCond
mrgSideCond ss (tvscs1,fvs1) (tvscs2,fvs2)
     = do tvscs' <- mrgTVarCondLists ss tvscs1 tvscs2
          mrgTVarFreshConditions ss (fvs1 `S.union` fvs2) tvscs'
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
scDischarge ss anteSC@(anteTVSC,anteFvs) cnsqSC@(cnsqTVSC,cnsqFvs)
  | isTrivialSC cnsqSC  =  return scTrue  -- (G => true) = true
  | isTrivialSC anteSC  =  return cnsqSC  -- (true => L) = L
  | otherwise
     = do tvsc' <- scDischarge' ss anteTVSC cnsqTVSC
          freshDischarge ss anteFvs cnsqFvs tvsc'
\end{code}

% We have a modified version of \texttt{Data.List.groupBy}
% \begin{code}
% groupByGV :: [TVarSideConds] -> [(GenVar,[TVarSideConds])]
% groupByGV []          =  []
% groupByGV (tvsc:tvscs)  =  (gv,tvsc:ours) : groupByGV others
%                       where
%                         gv               =  termVar tvsc
%                         gv `usedIn` tvsc  =  gv == termVar tvsc
%                         (ours,others)    =  span (usedIn gv) tvscs
% \end{code}

\subsection{Term-Variable  Condition  Discharge}

Now onto processing those ordered Term-Variable Side-Conditions:
\begin{code}
scDischarge'  :: MonadFail m => [Subscript]
              -> [TVarSideConds] -> [TVarSideConds]
              -> m [TVarSideConds]
scDischarge' _ _ []      =  return []     --  discharged
scDischarge' _ [] tvscL  =  return tvscL  --  not discharged
scDischarge' ss        (tvscG@(TVSC gvG _ _ _):restG) 
                tvscLs@(tvscL@(TVSC gvL _ _ _):restL)
  | gvG < gvL  =  scDischarge' ss restG tvscLs -- tvscG not needed
  | gvG > gvL  =  do -- nothing available to discharge tvscL
                     rest' <- scDischarge' ss restG restL
                     return (tvscsL++rest')
  | otherwise  =  do -- use tvscG to discharge tvscL
                     tvsc' <- tvscDischarge ss tvscG tvscL
                     rest' <- scDischarge' ss restG restL
                     return (tvsc':rest')
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
tvscDischarge :: MonadFail m => [Subscript]
              -> TVarSideConds -> TVarSideConds -> m TVarSideConds
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
tvscDischarge _ _ (TVSC (StdVar (Vbl _ ObsV _)) dL _ _)
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


Now, we work through the combinations:
\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true, \quad\IF\quad D_L \subseteq D_G
\\ & \mapsto & (D_L\setminus D_G) \disj V
\end{eqnarray*}
% \begin{code}
% ascDischarge ss (Disjoint u1 _ dG) (Disjoint u2 gv dL)
%   | linL `subset` linG  =  return [] -- true
%   | otherwise           =  return [gv `disjfrom` (linL `diff` linG)]
%   where
%     linG = (u1,lineariseVarSet dG)
%     linL = (u2,lineariseVarSet dL)
%     subset = isSCsubset ss
%     diff s t = packUG $ doSCdiff ss s t
% \end{code}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false,
     \quad\IF\quad C_L \subseteq D_G \land isStdObs(V)
\\ & \mapsto & (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
% \begin{code}
% ascDischarge ss (Disjoint u1 _ dG) cc@(CoveredBy u2 gv cL)
%   | linL `subset` linG
%     && isObsGVar gv     =  fail "Disj=>emptyCover"
%   | otherwise           =  return [gv `coveredby` (linL `diff` linG)]
%   where
%     linG = (u1,lineariseVarSet dG)
%     linL = (u2,lineariseVarSet cL)
%     subset = isSCsubset ss
%     diff s t = packUG $ doSCdiff ss s t
% \end{code}

\begin{eqnarray*}
   C_G \supseteq V \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad C_G \subseteq C_L
\\ & = & \false, \quad \IF \quad C_G \disj C_L \land isStdObs(V)
\\ & \mapsto & (C_G \cap C_L)\cup C_{?L} \supseteq V
\end{eqnarray*}
Here we have to ensure that $C_{?L}$ is retained, as no floating variables
exist in $C_G$, and so the intersection would remove those in $C_L$.
% \begin{code}
% ascDischarge ss (CoveredBy u1 _ cG) (CoveredBy u2 gv cL)
%   | linG `subset` linL                =  return []
%   | linG `disj` linL && isObsGVar gv  =  fail "CoverDisj=>noCover"
%   | otherwise  =  return
%                     [gv `coveredby` ((linG `intsct` linL) `union` linF)]
%   where
%     subset = isSCsubset ss
%     disj = isSCdisjoint ss
%     intsct = doSCint ss
%     union s t = packUG $ doSCunion ss s t
%     linG = (u1,lineariseVarSet cG)
%     linL = (u2,lineariseVarSet cL)
%     linF = (u2,lineariseVarSet $ S.filter isFloatingGVar cL)
% \end{code}


\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & = & \true, \quad \IF~ C_G\cap D_L = \emptyset
\\ & \mapsto & D_L \disj V
\end{eqnarray*}
% \begin{code}
% ascDischarge ss (CoveredBy u1  _ cG) d@(Disjoint u2  gv dL)
%   | linG `disj` linL  =  return []
%   | otherwise         =  return [d]
%   where
%     disj = isSCdisjoint ss
%     linG = (u1,lineariseVarSet cG)
%     linL = (u2,lineariseVarSet dL)
% \end{code}


Anything else is not handled right now;
\begin{code}
tvscDischarge _ _ tvscL = return tvscL
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
freshDischarge :: MonadFail m => [Subscript]
              -> VarSet -> VarSet -> [TVarSideConds] -> m SideCond
freshDischarge ss anteFvs cnsqFvs tvsc
  = do tvsc' <- freshDischarge' ss anteFvs tvsc
       return (tvsc' , cnsqFvs S.\\ anteFvs )
\end{code}

\begin{code}
freshDischarge' :: MonadFail m => [Subscript]
                -> VarSet -> [TVarSideConds] -> m [TVarSideConds]
freshDischarge' ss anteFvs [] = return []
freshDischarge' ss anteFvs (tvsc:tvscs)
  = do ascl  <- freshTVarDischarge ss anteFvs tvsc
       tvscs' <- freshDischarge'    ss anteFvs tvscs
       return (ascl++tvscs')
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
freshTVarDischarge :: MonadFail m => [Subscript]
                   -> VarSet -> TVarSideConds -> m [TVarSideConds]
\end{code}
We now consider the following possibilities:
\begin{eqnarray*}
   G_F \discharges D_L \disj V
   &=& \true, \quad \IF\quad D_L \subseteq G_F
\\ &\mapsto& D_L \setminus G_F \disj V
\end{eqnarray*}
% \begin{code}
% freshTVarDischarge ss gF (Disjoint u gv dL)
%   | linL `subset` linF  =  return []
%   | otherwise  =  return [gv `disjfrom` (linL `diff` linF)]
%   where
%     subset = isSCsubset ss
%     diff s t  = packUG $ doSCdiff ss s t
%     linF = (NonU,lineariseVarSet gF)
%     linL = (u,lineariseVarSet dL)
% \end{code}

\begin{eqnarray*}
   G_F \discharges C_L \supseteq V
   &\mapsto&  C_L \setminus G_F \supseteq V
\end{eqnarray*}
% \begin{code}
% freshTVarDischarge ss gF (CoveredBy u gv cL)
%   = return [gv `coveredby` (linL `diff` linF)]
%   where
%     diff s t = packUG $ doSCdiff ss s t
%     linF = (NonU,lineariseVarSet gF)
%     linL = (u,lineariseVarSet cL)
% \end{code}


Anything else is not handled right now.
\begin{code}
freshTVarDischarge ss gF tvsc = return [tvsc]
\end{code}


\newpage
\section{Check for Floating Conditions}

When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check that \emph{all} the term variable side-conditions in that residual
mention variables that are marked as ``floating''.
Only these can possibly be instantiated to satisfy the residual side-condition.
\begin{code}
isFloatingTVSC :: TVarSideConds -> Bool
isFloatingTVSC (TVSC  gv vsD mvsC mvsCd)
  = isFloatingGVar gv || 
    ( hasFloating vsD && hasFloatingM mvsC && hasFloatingM mvsCd )
hasFloating :: VarSet -> Bool
hasFloating vs = any isFloatingGVar $ S.toList vs
hasFloatingM :: Maybe VarSet -> Bool
hasFloatingM Nothing = False
hasFloatingM (Just vs) = hasFLoating vs
\end{code}
% One exception to this, during law matching,
% is that coverage may reduce to the empty set
% because unbound variables given a temporary binding
% to a ``?'' variable (\texttt{bindFloating})
% will not cancel out other variables that they should be able to do,
% if instantiated properly.
% \begin{code}
% tolerateAutoOrNull :: VarSet -> TVarSideConds -> Bool
% tolerateAutoOrNull unbound (TVSC _ vsD mvsC mvsCd) 
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
findGenVar :: MonadFail m => GenVar -> SideCond -> m TVarSideConds
findGenVar gv ( tvscs, _ )  =  findGV gv tvscs

findGV _ [] = fail "findGenVar: not in any term variable side-condition"
findGV gv (tvsc:tvscs)
  | gv `mentionedBy` tvsc  =  return tvsc
  | otherwise             =  findGV gv tvscs

mentionedBy :: GenVar -> TVarSideConds -> Bool
gv `mentionedBy` tvsc
  | otherwise      =  gv == termVar tvsc
\end{code}

We then look at returning all mentions of a variable:
\begin{code}
findAllGenVar :: GenVar -> SideCond -> [TVarSideConds]
findAllGenVar gv ( tvscs, _ )  =  findAGV gv [] tvscs

findAGV _ scsa []  =  reverse scsa
findAGV gv scsa (tvsc:tvscs)
  | gv `mentionedBy` tvsc  =  findAGV gv (tvsc:scsa) tvscs
  | otherwise             =  findAGV gv scsa       tvscs
\end{code}

We sometimes want mentions for a specific condition type:
\begin{code}
findCoveredGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findCoveredGenVar gv ( tvscs, _ ) = findCGV gv tvscs

findCGV gv []         =  fail ("Covered "++show gv ++ " not found")
findCGV gv ((TVSC gv' _ (Just vs) _):tvscs)
  | gv == gv'         =  return vs
findCGV gv (_:tvscs)  =  findCGV gv tvscs
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
\subsection{Side-Condition Subset Query}


\textbf{ALL NOW REDUNDANT AS UNIFORMITY COMPONENT NO LONGER EXISTS}

\begin{code}
isSCsubset :: [Subscript] -> ([[GenVar]]) -> ([[GenVar]])
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
isUGsubset :: [Subscript] -> ([GenVar]) -> ([GenVar])
           -> Bool
-- both GenVar lists are non-empty and ordered
-- all their contents have the same identifier and class
isUGsubset _  _             [_]     =  True
isUGsubset ss [_]    vl2        =  hasAllDynamics ss vl2
isUGsubset _  vl1@(_:_) vl2@(_:_)  =  vl1 `issubset` vl2

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
isSCdisjoint :: [Subscript] -> ([[GenVar]]) -> ([[GenVar]])
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
isUGdisjoint :: [Subscript] -> ([GenVar]) -> ([GenVar])
             -> Bool
-- both GenVar lists are non-empty and ordered
-- all their contents have the same identifier and class
-- If ui is Uniform, then GenVar_i is a singleton
isUGdisjoint _   vl1  vl2  =  vl1 `isdisj` vl2
isUGdisjoint _   _           _           =  False
\end{code}

\newpage
\subsection{Side-Condition Set Difference}

\begin{code}
doSCdiff :: [Subscript] -> ([[GenVar]]) -> ([[GenVar]])
         -> ([[GenVar]])
\end{code}

$$S \setminus \emptyset = S \qquad \emptyset \setminus S = \emptyset$$
\begin{code}
doSCdiff _ vls1 []  =  vls1
doSCdiff _ [] _   =  []
\end{code}

Otherwise, we walk through both sides
\begin{code}
doSCdiff ss ugs1 ugs2 = doSCdiff' ss [] ugs1 ugs2

doSCdiff' ss slv [] _  =  reverse slv

doSCdiff' ss slv vls1 [] = reverse slv ++vls1

doSCdiff' ss slv (g1@(gv1:vl1):vls1) (g2@(gv2:vl2):vls2)
  | gv1  < gv2  =  doSCdiff' ss (g1:slv) vls1 g2 -- keep g1
  | gv1  > gv2  =  doSCdiff' ss slv      ugs1      vls2
  | null g3     =  doSCdiff' ss slv      vls1 vls2  -- gv1 ~ gv2
  | otherwise   =  doSCdiff' ss (g3:slv) vls1 vls2  -- gv1 ~ gv2
  where
    g3 = doUGdiff ss g1 g2
\end{code}

Set difference given all with same identifier and class:
\begin{code}
doUGdiff :: [Subscript] -> ([GenVar]) -> ([GenVar])
         -> ([GenVar])
doUGdiff _  u1       _  =  []
doUGdiff ss [gv1] g2    =  genTheGenVars gv1 ss \\ g2
doUGdiff ss g1     g2    =  g1 \\ g2
\end{code}

\newpage
\subsection{Side-Condition Set Intersection}

\begin{code}
doSCint :: [Subscript] -> ([[GenVar]]) -> ([[GenVar]])
         -> ([[GenVar]])
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
doUGint :: [Subscript] -> ([GenVar]) -> ([GenVar])
         -> ([GenVar])
doUGint _  g1    [_]  =  g1
doUGint ss [_] g2   =  g2
doUGint ss g1     g2     =  g1 `intersect` g2
\end{code}



\newpage
\subsection{Side-Condition Set Union}


\begin{code}
doSCunion :: [Subscript] -> ([[GenVar]]) -> ([[GenVar]])
         -> ([[GenVar]])
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
doUGunion :: [Subscript] -> ([GenVar]) -> ([GenVar])
         -> ([GenVar])
doUGunion ss ug1@[_] _               =  ug1
doUGunion ss _              ug2@[_]  =  ug2
doUGunion ss g1         g2          =  g1 `union` g2
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
% return all TVSCs that mention any variable in that set:
% \begin{code}
% -- NOT USED ANYWHERE!
% citingASCs :: VarSet -> SideCond -> [TVarSideConds]
% citingASCs vs (sc,_) = filter (cited vs) sc
%
% cited :: VarSet -> TVarSideConds -> Bool
% vs `cited` tvsc  =  vs == tvscVSet tvsc
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
       ( tvscCheck [] (Disjoint NU  gv_a S.empty) @?= tstTrue )
    , testCase "v_e `disjoint` empty is True"
       ( tvscCheck [] (Disjoint NU  v_e S.empty) @?= tstTrue )
    , testCase "gv_a `disjoint` {gv_a} is False"
       ( tvscCheck [] (Disjoint NU  gv_a $ S.singleton gv_a) @?= tstFalse )
    , testCase "gv_a `disjoint` {gv_b} is True"
       ( tvscCheck [] (Disjoint NU  gv_a $ S.singleton gv_b) @?= tstTrue )
    , testCase "v_e `disjoint` {v_e} stands"
       ( tvscCheck [] (Disjoint NU  v_e $ S.singleton v_e)
         @?= tstWhatever  (Disjoint NU  v_e $ S.singleton v_e) )
    , testCase "v_e `disjoint` {v_f} stands"
       ( tvscCheck [] (Disjoint NU  v_e $ S.singleton v_f)
         @?= tstWhatever  (Disjoint NU  v_e $ S.singleton v_f) )
    , testCase "v_e `disjoint` {gv_a} stands"
       ( tvscCheck [] (Disjoint NU  v_e $ S.singleton gv_a)
         @?= tstWhatever  (Disjoint NU  v_e $ S.singleton gv_a) )
    , testCase "gv_a `disjoint` {v_f} stands"
       ( tvscCheck [] (Disjoint NU  gv_a $ S.singleton v_f)
         @?= tstWhatever  (Disjoint NU  gv_a $ S.singleton v_f) )
    , testCase "gv_a `disjoint` {gv_b,v_f} stands"
       ( tvscCheck [] (Disjoint NU  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (Disjoint NU  gv_a $ S.fromList [gv_b,v_f]) )
    ]

tst_scChkCovers
 = testGroup "CoveredBy NU  (no known vars)"
    [ testCase "gv_a `coveredby` empty is False"
       ( tvscCheck [] (CoveredBy NU  gv_a S.empty) @?= tstFalse )
    , testCase "v_e `coveredby` empty stands"
       ( tvscCheck [] (CoveredBy NU  v_e S.empty)
         @?= tstWhatever (CoveredBy NU  v_e S.empty) )
    , testCase "gv_a `coveredby` {gv_a} is True"
       ( tvscCheck [] (CoveredBy NU  gv_a $ S.singleton gv_a) @?= tstTrue )
    , testCase "gv_a `coveredby` {gv_b} is False"
       ( tvscCheck [] (CoveredBy NU  gv_a $ S.singleton gv_b) @?= tstFalse )
    , testCase "v_e `coveredby` {v_e} is True"
       ( tvscCheck [] (CoveredBy NU  v_e $ S.singleton v_e) @?= tstTrue )
    , testCase "v_e `coveredby` {v_f} stands"
       ( tvscCheck [] (CoveredBy NU  v_e $ S.singleton v_f)
         @?= tstWhatever  (CoveredBy NU  v_e $ S.singleton v_f) )
    , testCase "v_e `coveredby` {gv_a} stands"
       ( tvscCheck [] (CoveredBy NU  v_e $ S.singleton gv_a)
         @?= tstWhatever  (CoveredBy NU  v_e $ S.singleton gv_a) )
    , testCase "gv_a `coveredby` {v_f} stands"
       ( tvscCheck [] (CoveredBy NU  gv_a $ S.singleton v_f)
         @?= tstWhatever  (CoveredBy NU  gv_a $ S.singleton v_f) )
    , testCase "gv_a `coveredby` {gv_b,v_f} stands"
       ( tvscCheck [] (CoveredBy NU  gv_a $ S.fromList [gv_b,v_f])
         @?= tstWhatever  (CoveredBy NU  gv_a $ S.fromList [gv_b,v_f]) )
    ]
\end{code}

\subsection{Merging Tests}

\begin{code}
tst_mrgAtmCond :: TF.Test
tst_mrgAtmCond
 = testGroup "Merging Side-Conditions (no known vars)"
     [ testCase "merge gv_a `disjoint` empty  into [] is True"
        ( mrgTVarConds [] (Disjoint NU  gv_a S.empty) [] @?= Just [] )
     , testCase "merge gv_a `disjoint` {gv_a} into [] is False"
        ( mrgTVarConds [] (Disjoint NU  gv_a $ S.singleton gv_a) [] @?= Nothing )
     , testCase "merge v_e `coveredby` {v_f}  into [] is [itself]"
        ( mrgTVarConds [] (CoveredBy NU  v_e $ S.singleton v_f) []
          @?= Just [CoveredBy NU  v_e $ S.singleton v_f] )
     , testCase "merge gv_a `disjoint` empty  into [tvsc(gv_b)] is [tvsc(gv_b)]]"
        ( mrgTVarConds [] (Disjoint NU  gv_a S.empty) [tvsc1] @?= Just [tvsc1] )
     , testCase "merge gv_a `disjoint` {gv_a} into [tvsc(gv_b)] is False"
        ( mrgTVarConds [] (Disjoint NU  gv_a $ S.singleton gv_a) [tvsc1] @?= Nothing )
     , testCase
        "merge v_e `coveredby` {v_f}  into [tvsc(gv_b)] is [tvsc(gv_b),itself]"
        ( mrgTVarConds [] (CoveredBy NU  v_e $ S.singleton v_f) [tvsc1]
          @?= Just [tvsc1,CoveredBy NU  v_e $ S.singleton v_f] )
     ]

tvsc1 = (CoveredBy NU  gv_b $ S.fromList [gv_b,v_f])
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
