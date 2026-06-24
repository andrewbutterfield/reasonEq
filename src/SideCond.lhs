\chapter{Side Conditions}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-2026

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond (
  disjfrom, coveredby, dyncovered
-- , simplifyVSetPred
, SideCond(..), scVSPreds, scFVars
, scTrue
, isTrivialSC -- used just here and in TestRendering !!!!
, mrgVarConds -- AbstractProver  (xtndCoverage for float replacements) ?
--, mergeVarConds -- not used elsewhere!
, mrgSideCond -- AbstractProver - KEEP
, mkSideCond -- Instantiate, Assertions, SourceHandling - KEEP
, scDischarge -- AbstractProver, LiveProofs - KEEP
, isFloatingVSC -- LiveProofs - KEEP
, addFreshVars, onlyFreshSC -- AbstractProver - KEEP
, notin, covers, dyncover, fresh -- builtins,etc., - KEEP
, findGenVarInSC  -- Substitution - KEEP
, findAllGenVar -- Instantiate - KEEP for now
, findCoveredGenVar -- FreeVars - KEEP for now
, mentionedBy -- Substitution - KEEP
-- below, unsafe, testing or builtins only
, (.:), mrgscs -- both unsafe, latter is mrgSideCond*s* 
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
import VarSetPred


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
(e.g. $\fv(T) \disj x \land \fv(T) = x$, always ``false'').
As a false side-condition means a match failure,
we do not represent them explicitly.
Instead, any operation on side-conditions that could result
in an inconsistent result should fail, gracefully.

NEW: the term $T$ is represented using the \texttt{StdVar} variant of a 
\texttt{GenVar}. 
However there are emerging use cases that want to relate a list-variable with a
set of general variables. 
These crop up in the UTCP theory when defining $X(E|R|a|N)$,
such as $E \disj \lst O,\lst O'$, 
where $E$ is  (set-valued) expression variable.

\subsection{Term (List-Variable?)/Variable-Set Relations}

An term variable side-condition (VSC) can have one of the following forms,
where $T$ abbreviates $\fv(T)$:
\begin{eqnarray*}
   T \disj x,\lst v
   && \mbox{disjoint, short for }\fv(T) \cap \{x,\lst v\} = \emptyset
\\ T \subseteq x,\lst v 
   && \mbox{covering, short for }\fv(T) \subseteq \{x,\lst v\}
\\ T \subseteq_d  x_d,\lst v_d
   && \mbox{dynamic coverage, short for } \dfv(T) \subseteq \{x_d,\lst v_d\}
\\ pre      \subseteq T && \mbox{pre-condition, no dashed variables}
\end{eqnarray*}
The dynamic variables here correspond to what UTP calls the ``alphabet''
of a predicate, hence the use of subscript `a'.`
For dynamic coverage, a fuller more rigorous definition is:
\begin{equation*}
T \subseteq_d V
\quad\defs\quad 
(\forall g \in V \bullet \isdyn(g))
\land
\dfv(T) \subseteq V
\end{equation*}
\textbf{
NOTE: 
The above definition evaluates to false if $V$ contains any non-dynamic variables.
An alternative definition is that we restrict both sides to dynamic variables,
before doing the check. 
Which is better? Which is correct?
}


In most cases the term $T$ will be very general,
and will be represented by a variable.
In some cases, we will use a list-variable to denote a list of terms,
usually expressions, and we will expect there to be only one general variable
which will itself be a list variable:
\begin{eqnarray*}
   \lst v   \disj  \lst e && \mbox{disjoint, short for }
   \fv(e_1) \disj v_1\disj \land \dots \land \fv(e_n) \disj v_n 
\end{eqnarray*}
This arises when we have side-conditions between lists of variables
and expressions that occur in substitutions.

We note that disjointness and being a (pre-)condition
distribute through conjunction without restrictions,
so we have, for example, that:
\begin{eqnarray*}
   S,T \disj x,y 
   &\equiv&
   x \disj S \land x \disj T \land y \disj S \land y \disj T
\\ S,T \subseteq pre
   &\equiv&
   S \subseteq pre \land T \subseteq pre
\end{eqnarray*}
However, covering only distributes (like $pre$) w.r.t. conjunction
as far as terms are concerned.
The variable-list must be retained as a unit.
\begin{eqnarray*}
   S,T \subseteq x
   &\equiv&
   S\subseteq x \land T \subseteq x
\\ T \subseteq x,y
   &\not\equiv&
   T\subseteq x \land T \subseteq y
\end{eqnarray*}
In general we are assuming that law side-conditions have term variables,
but when we instantiate such side-conditions with a match binding,
we may find observational variables appearing.
In some of these cases, we may be able to simplify a side-condition further:
\begin{eqnarray*}
   z \disj \dots,z,\dots        && \false
\\ z \subseteq \dots,z,\dots{}  && \true
\\ z \subseteq \emptyset        && \false
\\ z \subseteq_d \emptyset      && \lnot\isdyn(z)
\\ z \subseteq pre              && z \textrm{ is a \texttt{Before} variable}
\end{eqnarray*}
For list variables, we can add:
\begin{eqnarray*}
   \lst\ell\less x,\dots \subseteq \lst\ell   && \true
\\ \lst\ell\less x,\dots \subseteq_d \lst\ell   && \isdyn(\lst\ell)
\end{eqnarray*}

We also need to take account of known variables of various kinds
when evaluating and building side-conditions.


\section{Variable Side-Conditions (VSC)}

We now introduce our notion of variable side-conditions.
We will not represent $pre$ explicitly here,
and instead will use $T \subseteq \lst O$.
Our basic VSC is implemented using \h{VSetPred},
and are built up from three basic forms,
each of which will relate a \emph{single} global (term) 
variable to a variable set:
$$
   \setof{v_G} \disj S \qquad  v_G 
$$

\subsection{VSC Builders}

We provide some builders for the three conditions:
\begin{code}
disjfrom, coveredby, dyncovered :: GenVar -> VarSet -> VSetPred
gv `disjfrom`   vsD   =  VSDisj gv vsD
gv `coveredby`  vsC   =  VSSub  gv vsC
gv `dyncovered` vsCd  =  VSSubD gv vsCd
\end{code}

\newpage
\subsection{VSC Queries}

\begin{code}
termVar :: MonadFail mf => VSetPred -> mf GenVar
termVar (VSDisj gv _)  =  return gv
termVar (VSSub  gv _)  =  return gv
termVar (VSSubD gv _)  =  return gv
termVar vsp            =  fail "no term-var involved"

theSetExpr :: MonadFail mf => VSetPred -> mf VarSet
theSetExpr (VSDisj _ s2)  =  return s2
theSetExpr (VSSub  _ s2)  =  return s2
theSetExpr (VSSubD _ s2)  =  return s2
theSetExpr vsp            =  fail "no set-expression involved"
\end{code}

\section{VSC Laws}

We want to specify side-conditions by lists of \h{VSetPred}.
However we want to ``normalise'' these, 
by ordering them by the global variable,
and by reducing all the conditions, for a given such variable, 
down to  a normal form (at most exactly one each of \h{VS(Disj|Sub|SubD)}).

The starting point is a sorted list of \h{VSetPred} 
of the form $\setof{g} ~rel~ E$,
where $g$ is a general variable, and $E$ is a \h{VarSet}.
The sortedness means that for each distinct variable $g_i$ we will have
a sequence of $\setof{g_i}rel_1{E_1}~;\dots;~\setof{g_i}rel_n{E_n}$.
This sequence will be ordered by the relations ($rel_1,\dots,rel_n$)
drawn from the three available relations, 
themselves ordered as $\disj,\subseteq,\subseteq_d$.
In effect, the list $rel_1,\dots,rel_n$ has the form:
$\disj_1,\dots,\disj_i
,\subseteq_1,\dots,\subseteq_j
,\subseteq_{a_1},\dots,\subseteq_{a_k}$
where $i,j,k, \geq 0$ and $n=i+j+k$.


\subsection{Assembling \protect\h{VSetPred} Lists}

We want to specify side-conditions by lists of \h{VSetPred}.
However we want to ``normalise'' these, 
by ordering them by the global variable,
and by reducing all the conditions, for a given such variable, 
down to  a normal form (at most exactly one each of \h{VS(Disj|Sub|SubD)}).
In effect we try to shrink the enumerations involved.
We start with some same-predicate simplification laws,
that reduce a list of predicates with the same relation down to 
a single instance of that relation.
At this stage we have $i,j,k \leq 1$,
and then add the following four different-predicate normalising laws,
that combine and simplify relations as much as possible.
So we should only use $\subseteq$ with \h{Static} $g$,
and $\subseteq_d$ with dynamic $g_d$.

Here we are generally interested in single relations 
($\disj$,$\subseteq$,$\subseteq_d$)
with a single distinguished term variable $g$ embedded inside set operations ($\cup$,$\setminus$).
We want to pull $g$ out to be the sole 1st argument of the relation.
These should \emph{not} reduce the relations to \true\ or \false.
In general we may need extra terms not involving $g$ in the output.
We want to distinguish these so we keep them separate.
This leads to the following predicate-splitting laws:
\begin{eqnarray*}
   (g \setminus X)     \disj Y &=& g \disj (Y \setminus X)
\\ (g \cup X)          \disj Y &=& (g \disj Y) \land (X \disj Y)
\\ (g \setminus X) \subseteq Y &=& g \setminus (X \cup Y) \subseteq \emptyset
\\ (g \cup X)      \subseteq Y &=& g \subseteq Y \land X \subseteq Y
\\ (g \setminus X) \subseteq_d Y &=& g \setminus (X \cup Y) \subseteq_d \emptyset
\\ (g \cup X) \subseteq_d Y &=& g \subseteq_d Y \land X \subseteq_d Y
\end{eqnarray*}


% \begin{code}
% simplifyVSetPred :: VSetPred -> (VSetPred,[VSetPred])
% \end{code}  

% \subsection{Union and Diff vs. Disjoint and Superset}

% We have the following variations:


% $$(g \setminus X) \disj Y ~=~ g \disj (Y \setminus X)$$
% \begin{code}
% simplifyVSetPred ((g `vsMinus` x) `VSDisj` y)  
%              =  ( g `VSDisj` (y `vsMinus` x) , [] )
% \end{code} 

% $$ 
%    (g \cup X) \disj Y 
%    ~=~ 
%    (g \disj Y) \land (X \disj Y)
% $$
% \begin{code}
% simplifyVSetPred ((g `vsUnion` x) `VSDisj` y)  
%                = ( g `VSDisj` y , [x `VSDisj` y ] )
% \end{code} 

% $$  
%    (g \setminus X) \subseteq Y
%    ~=~ 
%    g \setminus (X \cup Y) \subseteq \emptyset
% $$
% \begin{code}
% simplifyVSetPred ((g `vsMinus` x) `VSSub` y) 
%   = ( g `vsMinus` (x `vsUnion` x) `VSSub` vsEmpty , [] )
% \end{code} 

% $$ (g \cup X) \subseteq Y
%    ~=~ 
%    g \subseteq Y \land X \subseteq Y
% $$
% \begin{code}
% simplifyVSetPred ((g `vsUnion` x) `VSSub` y)  
%              =  ( g `VSSub` y , [x `VSSub` y] )
% \end{code} 


% \subsection{Union and Diff vs. Dynamic Superset}

% Reminder: Dynamic subset ($\subseteq_d$) is defined as:
% $$
%   g \subseteq_d X \quad \defs \quad g|d \subseteq X|d
% $$

% $$  
%    (g \setminus X) \subseteq_d Y
%    ~=~ 
%    g \setminus (X \cup Y) \subseteq_d \emptyset
% $$
% \begin{code}
% simplifyVSetPred ((g `vsMinus` x) `VSSubD` y) 
%   = ( g `vsMinus` (x `vsUnion` x) `VSSubD` vsEmpty , [] )
% \end{code} 

% $$ (g \cup X) \subseteq_d Y
%    ~=~ 
%    g \subseteq_d Y \land X \subseteq_d Y
% $$
% \begin{code}
% simplifyVSetPred ((g `vsUnion` x) `VSSubD` y)  
%              =  ( g `VSSubD` y , [x `VSSubD` y] )
% \end{code} 

% \subsection{All other cases: no change}

% For now we notice that that none of the laws above
% introduce intersections or disjunctions.
% We'll only add laws about those if they arise elsewhere.
% \begin{code}
% simplifyVSetPred vse = (vse,[]) 
% \end{code}  


% The key trick is to take \m{g ~R~ \setof{g_1,\dots,g_n}}
% and break it down into individual comparisons (\m{g ~R~ \setof{g_i}}).

% \newpage
% \subsubsection{Checking Disjoint $ V \disj g$}

% Here, checking \m{g \disj \setof{g_1,\dots,g_n}}
% reduces to checking \m{\bigwedge_{i \in 1\dots n}(g \disj g_i)}.
% \begin{itemize}
%   \item definitely \false : \m{g = g_i}
%   \item definitely \true : \m{g} and \m{g_i} 
%      are both dynamic and have different dynamicity.
% \end{itemize}
% \begin{code}
% disjointCheck  :: MonadFail m => GenVar -> VarSet -> m VarSet
% disjointCheck gv NA         =  return disjNA
% disjointCheck gv (The vsD) = do
%   checked  <-  disjCheck gv S.empty $ S.toList vsD
%   return $ The checked


% disjCheck :: MonadFail m
%           => GenVar -> VarSet -> [GenVar] -> m VarSet
% disjCheck gv vsd [] = return vsd
% disjCheck gv vsd (gvd:gvs)
%   | gv == gvd             =  fail "disjCheck: same variable"
%   | gvw /= gvdw && bothd  =  disjCheck gv vsd                gvs
%   | otherwise             =  disjCheck gv (S.insert gvd vsd) gvs
%   where
%     gvw = gvarWhen gv
%     gvdw = gvarWhen gvd
%     bothd = isDynamic gvw && isDynamic gvdw
% \end{code}


% \subsubsection{Checking CoveredBy $V \supseteq g$}

% We may have \m{V} as the universal set, in which case  we return true.
% Otherwise, we can reduce checking \m{\setof{g_1,\dots,g_n} \supseteq g}
% to checking \m{\bigvee_{i \in 1,\dots,n} g = g_i \lor g \in g_i}.
% However we need to keep in mind that \m{g} can denote the universal set.

% \begin{code}
% coveredByCheck :: MonadFail m => GenVar -> VarSet -> m VarSet

% coveredByCheck gv NA  =  return covByNA  -- gv `coveredby` U
% coveredByCheck gv jvsC@(The vsC)
%   = covByCheck gv S.empty $ S.toList vsC
% \end{code}
% We work through the variable-set, looking for the genvar.
% We remove any observables that can't match.
% Failure occurs if the genvar is an observable and the ending var-set is empty.
% \begin{code}
% covByCheck :: MonadFail m => GenVar -> VarSet -> [GenVar] -> m VarSet

% covByCheck gv vsp []
%   | S.null vsp && isObsGVar gv  = fail "covered by nothing" 
%   -- term-vars,list-vars may evaluate to the empty-set, in which case this is true
%   | otherwise  = return $ The vsp
% covByCheck gv vsp (gvc:gvs)
%   | gv == gvc       =  return covByNA 
%   | lvCovBy gv gvc  =  return covByNA
%   | isObsGVar gv && isObsGVar gvc  =  covByCheck gv vsp gvs
%   -- if either is termvar then gv could be covered by gvs
%   | otherwise       =  covByCheck gv (S.insert gvc vsp) gvs
% \end{code}
% Is $\ell\less V$ covered by $\kappa\less W$ ?
% It is if $\ell=\kappa$ and $W \subseteq V$.
% \begin{code}
% lvCovBy :: GenVar -> GenVar -> Bool
% lvCovBy (LstVar (LVbl v is js)) (LstVar (LVbl covv isv jsv))
%   = v == covv && isv `issubset` is && jsv `issubset` js
% lvCovBy _ _ = False
% \end{code}


% \newpage
% \subsubsection{Checking DynamicCoverage $V \supseteq_a g$}


% We first check that all of $V$ is dynamic:
% \begin{eqnarray*}
%    \exists g_i \in V \bullet \lnot\isdyn(g_i) && \false
% \end{eqnarray*}
% We can reduce checking \m{\setof{g_1,\dots,g_n} \supseteq g}
% to checking \m{\bigvee_{i \in 1,\dots,n} g = g_i \lor g \in g_i}.

% Assuming $\forall v \in V \bullet \isdyn(v)$ we then proceed:
% \begin{eqnarray*}
%    \emptyset             \supseteq_a z   &&  \lnot\isdyn(z)
% \\ O,O' \supseteq_a V &&  
%         \true, \quad \IF \quad V \subseteq O \cup O' \cup ObsV
% \\ \lst\ell\setminus Z \supseteq_a \lst\ell\setminus (Z\cup W) 
%                                          &&  \true
% \\ \dots,g,\dots{}       \supseteq_a g   &&  \true
% \\ \{stdObs\}\setminus z \supseteq_a z   &&  \false
% \end{eqnarray*}

% Here, as $T$ could be empty,
% we cannot deduce that $\emptyset \supseteq T$ is false.
% Similarly, $T \supseteq z$ could also be true.
% \begin{code}
% dynCvrgCheck :: MonadFail m => GenVar -> VarSet -> m VarSet

% dynCvrgCheck gv NA  =  return covByNA
% dynCvrgCheck gv jvsCd@(The vsCd)
%   | notAllDyn  =  report "tvar dyncover fails (static)"
% --  | otherwise  = covByCheck gv S.empty $ S.toList vsCd
%   | any (lvCovBy gv) vsCd   =  return covByNA
%   | not $ isObsGVar gv      =  return jvsCd
%   | S.null vsCd 
%       =  if isDynGVar gv
%          then report "atomic dyncover fails (null)"
%          else return jvsCd
%   | all isStdV vsCd         =  report "tvar dyncover fails (all std)"
%   where 
%     notAllDyn = not $ all isDynGVar vsCd
%     showsv = "gv = "++show gv
%     showvs = "vsCd = "++show vsCd
%     report msg = fail $ unlines' [msg,showsv,showvs]
% dynCvrgCheck _ nvsCd  =  return nvsCd
% \end{code}



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
data SideCond 
  = SCD [VSetPred] VarSet
  deriving (Eq,Ord,Show)

instance Read SideCond where

  readsPrec _ str = [readSideCond str]

-- SCD [...] (fromList [...])
readSideCond :: String -> (SideCond,String)
readSideCond str
 | before3 == "SCD" = readSC1 after3
 | otherwise  
   =  error ("readSideCond, SCD expected, saw: \""++take 100 str++"\"")
 where (before3,after3) = splitAt 3 str

-- [...] (fromList [...])
readSC1 :: String -> (SideCond,String)
readSC1 (c:str) | isSpace c = readSC1 str
readSC1 str
  = case readsPrec 0 str of
      ((vsps,str'):_) -> readSC2 vsps str'
      _               -> error ("readSC1, [VSetPred] expected, seen: '"++str)

-- (fromList [...])
readSC2 :: [VSetPred] -> String -> (SideCond,String)
readSC2 vsps str@(c:str') 
  | isSpace c = readSC2 vsps str'
  | before10 == "(fromList " = readSC2' vsps after10
  where (before10,after10) = splitAt 10 str
readSC2 _ str = error ("readSC2, (fromList [VarSet]) expected, seen: '"++str)

-- [...])
readSC2' :: [VSetPred] -> String -> (SideCond,String)
readSC2' vsps str 
  = case readsPrec 0 str of
      ((fvl,str'):_)  -> readSC2'' (SCD vsps (S.fromList fvl)) str'
      _               -> error ("readSC2', [VarSet]) expected, seen: '"++str)

-- )
readSC2'' :: SideCond -> String -> (SideCond,String)
readSC2'' sc (')':str) = (sc,str)
readSC2'' sc str =   error ("readSC2'', close-par expected, seen: '"++str)

sN = vsSngl gN
sEdN  = VSDisj gE sN
sEsN  = VSSub  gE sN
sEsdN = VSSubD gE sN

scVSPreds :: SideCond -> [VSetPred]
scVSPreds (SCD vsps _)  =  vsps

scFVars :: SideCond -> VarSet
scFVars (SCD _ fvs)  =  fvs
\end{code}

If the term variable condition list is empty,
then we have the trivial side-condition, which is always true:
\begin{code}
scTrue :: SideCond
scTrue = SCD [] S.empty

isTrivialSC :: SideCond -> Bool
isTrivialSC (SCD [] fvs)  =  S.null fvs
isTrivialSC _             =  False
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
            => VSetPred -> [VSetPred] -> m [VSetPred]
\end{code}
\textbf{Invariant}\\
For \texttt{mrgVarConds vsp vsps} we have:\\
\texttt{vsps} is ordered, and\\
for all adjacent vsp with the same genvar, 
they have been simplified.



Now we search to see if there is a VSCs with the
same general-variable, respecting the ordering:
\begin{code}
mrgVarConds vsp' []  = return [vsp']

mrgVarConds vsp' vsps@(vsp1:vsps') = do
  v' <- termVar vsp'
  v1 <- termVar vsp1
  case compare v' v1 of
    LT  ->  return (vsp':vsps)
    GT  ->  do vsps'' <- mrgVarConds vsp' vsps'
               return ( vsp1 : vsps'' )
    EQ  ->  case mrgSameGVSC vsp' vsp1 of
      Nothing          ->  fail "mgrTVarConds: false s.c."
      Just []          ->  return vsps' -- mrg is true 
      Just [vsp'']     ->  return (vsp'':vsps')
      Just [vspA,vspB] -> do
        vsps'' <- mrgVarConds vspB vsps'
        return (vspA : vsps'')
\end{code}

\subsection{Merging two (checked) VSCs}

The semantics of the disjoint ($D$), covering ($C$),
and dynamic covering ($C_d$) variable-sets,
parameterised by a general variable $G$,
are:
\begin{eqnarray*}
  \sem{\_}_{\_} &:& \power V \fun V \fun \Bool
\\ \sem{D}_G &=& \fv.G \cap D = \emptyset
\\ \sem{C}_G &=& \fv.G \subseteq C
\\         &=& \fv.G = \emptyset, \quad \IF \quad C = \emptyset
\\ \sem{C_d}_G &=& \dfv.G \subseteq C_d \land \forall_{\isdyn}(C_d)
\\             &=& \dfv.G = \emptyset, \quad \IF \quad C_d = \emptyset
\end{eqnarray*}
In the sequel we assume: $\forall_{\isdyn}(C_d)$




Here we perform trying to merging an VSC in with another VSC 
referring to the same general variable (\h{gv}).
If two predicates are returned, they have the same general variable,
but a different predicate. They are both returned, simplified and sorted.

We work through every combination of two VSCs,
ensuring they follow the ordering $D;C;C_d$.
\begin{code}
mrgSameGVSC :: MonadFail m 
            => VSetPred -> VSetPred -> m [VSetPred]
\end{code}

$D_1 \times D_2$
\begin{eqnarray*}
   \fv.G \cap D_1 = \emptyset \land \fv.G \cap D_1 = \emptyset 
   &\equiv&  \fv.G \cap (D_1 \cup D_2) = \emptyset
\end{eqnarray*}
\begin{code}
mrgSameGVSC (VSDisj gv vsD1) (VSDisj _ vsD2) 
                                   = return [VSDisj gv (vsD1 `S.union` vsD2)]
\end{code}

$D \times C \qquad D \times C_d$
\begin{eqnarray*}
   \fv.G \cap D = \emptyset \land \fv.G \subseteq C
   &\equiv&  \fv.G \cap D = \emptyset \land \fv.G \subseteq (C\setminus D)
\\ \fv.G \cap D = \emptyset \land \fv.G \subseteq C_d
   &\equiv&  \fv.G \cap D = \emptyset \land \fv.G \subseteq (C_d\setminus D)
\end{eqnarray*}
\begin{code}
mrgSameGVSC vspDisj@(VSDisj gv vsD) (VSSub _ vsC) 
                                   = return [vspDisj,VSSub gv (vsC S.\\ vsD)]
mrgSameGVSC vspDisj@(VSDisj gv vsD) (VSSubD _ vsCd) 
                                 = return [vspDisj,VSSubD gv (vsCd S.\\ vsD)]
\end{code}

$C_1 \times C_2 \qquad Cd_1 \times Cd_2$
\begin{eqnarray*}
   \fv.G \subseteq C_1 \land \fv.G \subseteq C_2 &=&  \fv.G \subseteq (C_1 \cap C_2)
\\ \fv.G \subseteq Cd_1 \land \fv.G \subseteq Cd_2 &=&  \fv.G \subseteq (Cd_1 \cap Cd_2)
\end{eqnarray*}
\begin{code}
mrgSameGVSC (VSSub gv vsC1) (VSSub _ vsC2)
                             = return [VSSub gv (vsC1 `S.intersection` vsC2)]
mrgSameGVSC (VSSubD gv vsCd1) (VSSubD _ vsCd2)
                           = return [VSSub gv (vsCd1 `S.intersection` vsCd2)]
\end{code}

$C \times D \qquad C_d \times D$
\begin{eqnarray*}
   \fv.G \subseteq C \land \fv.G \cap D = \emptyset
   &=&  \fv.G \cap D = \emptyset \land \fv.G \subseteq (C \setminus D)
\\ \fv.G \subseteq C_d \land \fv.G \cap D = \emptyset
   &=&  \fv.G \cap D = \emptyset \land \fv.G \subseteq (C_d \setminus D)
\end{eqnarray*}
\begin{code}
mrgSameGVSC vspSub@(VSSub _ vsC1) vspDisj@(VSDisj gv vsD2)
                                 = return [vspDisj,VSSub gv (vsC1 S.\\ vsD2)]
mrgSameGVSC vspSub@(VSSubD _ vsCd1) vspDisj@(VSDisj gv vsD2)
                               = return [vspDisj,VSSubD gv (vsCd1 S.\\ vsD2)]
\end{code}

$C \times C_d \qquad C_d \times C$
\begin{eqnarray*}
   \fv.G \subseteq C \land \fv.G \subseteq C_d 
   &=?&  \fv.G \subseteq (C \setminus C_d) 
        \land  \fv.G \subseteq C_d 
\\ \fv.G \subseteq C_d \land \fv.G \subseteq C 
   &=?&  \fv.G \subseteq (C \setminus C_d) 
        \land  \fv.G \subseteq C_d 
\end{eqnarray*}
This is unclear. 
$C_d$ only contains (and cares about) dynamic variables.
$C$ can be a mix and cares precisely about those.

For now, we fudge, and just re-order them if needed.
\begin{code}
mrgSameGVSC vspSubD@(VSSubD _ _) vspSub  =  return [vspSub,vspSubD]
mrgSameGVSC vspSub vspSubD               =  return [vspSub,vspSubD]
\end{code}


\subsection{Merging Term-Var Side-Condition Lists}

We check for side-conditions that are trivially true,
as sometimes these result from instantiating law side-conditions
with match bindings.
\begin{code}
mrgTVarCondLists :: MonadFail m 
                 => [VSetPred] -> [VSetPred] -> m [VSetPred]
mrgTVarCondLists vsps1 []  =  return vsps1
mrgTVarCondLists [] vsps2  =  return vsps2
mrgTVarCondLists (vsp:vsps1) vsps2
  | (vsp == VSTrueP)  =  mrgTVarCondLists vsps1 vsps2
  | otherwise = do 
      vsps2' <- mrgVarConds vsp vsps2 
      mrgTVarCondLists vsps1 vsps2'
\end{code}

\subsection{Merging Term Variable and Freshness Side-Conditions}


\begin{code}
mrgTVarFreshConditions :: MonadFail m 
                       => VarSet -> [VSetPred] 
                       -> m SideCond
mrgTVarFreshConditions freshvs vsps
  | freshvs `disjoint` coveredVarsOf vsps  =  return $ SCD vsps freshvs
  -- the above might not work - `disjoint` may need more information
  | otherwise  =  fail "Fresh variables cannot cover terms."

coveredVarsOf :: [VSetPred] -> VarSet
coveredVarsOf vsps = S.unions $ map vPredVars vsps
\end{code}

\section{From VSC and Free-list to Side-Condition}

\begin{code}
mkSideCond :: MonadFail m 
           => [VSetPred] -> VarSet -> m SideCond
mkSideCond vsps fvs
 = do vsps' <-  mrgTVarCondLists vsps []
      mrgTVarFreshConditions fvs $ filter (not . (== VSTrueP)) vsps'
\end{code}


\subsection{Merging Full Side-conditions}

Merging two side-conditions is then straightforward,
simply merge each VSC and fresh set from the one into the other,
one at a time.
\textbf{Note: \h{mrgSideCond} is NOT commutative, and can be lossy}.
\begin{code}
mrgSideCond :: MonadFail m 
            => SideCond -> SideCond -> m SideCond
mrgSideCond (SCD vsps1 fvs1) (SCD vsps2 fvs2)
     = do vsps' <- mrgTVarCondLists vsps1 vsps2
          mrgTVarFreshConditions (fvs1 `S.union` fvs2) vsps'
          -- the above may require a obsv-savvy union?

mrgSideConds :: MonadFail m => [SideCond] -> m SideCond
mrgSideConds []        = return scTrue
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
  \item[Closure.{[}{]}\_def]
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
We first check for trivial side-conditions on either side,
and then process the variable side-conditions first,
the finishing off by processing the fresh variables:
\begin{code}
scDischarge obsv anteSC@(SCD anteVSC anteFvs) cnsqSC@(SCD cnsqVSC cnsqFvs)
  = if isTrivialSC cnsqSC then return scTrue
    else if isTrivialSC anteSC then return cnsqSC
    else do vsp' <- scDischarge' obsv anteVSC cnsqVSC
            freshDischarge obsv anteFvs cnsqFvs vsp'
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
% vscMrg (vsp:vsps) = mrgVarConds vsp vsps    
% \end{code}

\subsection{Term-Variable  Condition  Discharge}

Now onto processing those ordered Term-Variable Side-Conditions:
\begin{code}
scDischarge'  :: MonadFail m => VarSet
              -> [VSetPred] -> [VSetPred]
              -> m [VSetPred]
scDischarge' _ _ []      =  return []     --  discharged
scDischarge' _ [] vspL  =  return vspL  --  not discharged
scDischarge' obsv       (vspG:restG) -- ante
                  vspLs@(vspL:restL) -- cnsq
  = do  gvG <- termVar vspG ; gvL <- termVar vspL
        case compare gvG gvL of
          LT  ->  scDischarge' obsv restG vspLs -- vspG not needed
          GT  ->  do -- nothing available to discharge vspL
                     rest' <- scDischarge' obsv restG restL
                     return (vspL:rest')
          EQ  ->  do -- use vspG to discharge vspL
                     vsp' <- vspDischarge obsv vspG vspL
                     rest' <- scDischarge' obsv restG restL
                     return (vsp':rest')
\end{code}
\textbf{Any occurrences of a floating variable in a translated law side-condition
should be retained.
We let $D_{?L}$ and $C_{?L}$ denote
the floating subsets of $D_L$ and $C_L$ respectively.
Note sure if VSP Discharge below ensures this?}

\newpage
\subsubsection{VSP Discharge}

At this point we have the form, for given (usually term) variable $V$:
\begin{equation}
 \left( V ~rel~ S_G\right)
 \vdash
 \left( V ~rel~ S_L\right)
\end{equation}
Finally, we have arrived at where the real work is done.

\begin{code}
vspDischarge  :: MonadFail m 
              => VarSet
              -> VSetPred -> VSetPred 
              -> m VSetPred
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

The following case needs special treatment:

A translated law side-condition of the form $\emptyset \supseteq v$,
where $v$ is a standard variable.
This is simply false.
\begin{code}
vspDischarge obsv _ (VSSub (StdVar (Vbl _ ObsV _)) vsC)
  | S.null vsC  =  fail ("Empty set cannot cover a standard obs. variable")
\end{code}

\subsubsection{Pairwise Discharging (C:C) and (Cd:Cd)}

We start with the \m{C} and \m{Cd} components because $\subseteq$
is strong enough to potentially falsify some side-conditions, 
whereas $\disj$ is too weak for this.

\begin{eqnarray*}
   C_G \supseteq V \discharges C_L \supseteq V
   & = & \true, \quad \IF \quad C_G \subseteq C_L
\\ & = & \false, \quad \IF \quad C_G \disj C_L \land isObsVar(V)
\\ & = & (C_G \cap C_L)\cup C_{?L} \supseteq V, \quad \textbf{otherwise}
\end{eqnarray*}
Edge cases:
  If \m{V} is a term variable, 
  then it is possible that \m{\fv(V)=\emptyset},
  in which case the fact that \m{C_G \disj C_L} is irrelevant.
\begin{code}
vspDischarge obsv (VSSub gv vsCG) predL@(VSSub _ vsCL)
  | S.null vsCG                             =  return predL
  | vsCG `S.isSubsetOf` vsCL                =  return VSTrueP 
  | vsCL `S.disjoint` vsCG && isObsGVar gv  =  fail "discharge CC false"
  | otherwise  
          = return $ VSSub gv ((vsCG `S.intersection` vsCL) `S.union` vsCLf)
  where vsCLf = S.filter isFloatingGVar vsCL
vspDischarge obsv (VSSubD gv vsCdG) predL@(VSSubD _ vsCdL)
  | S.null vsCdG                            = return predL
  | vsCdG `S.isSubsetOf` vsCdL              = return VSTrueP 
  | vsCdL `S.disjoint` vsCdG && isObsGVar gv = fail "discharge CdCd false"
  | otherwise  
       = return $ VSSubD gv ((vsCdG `S.intersection` vsCdL) `S.union` vsCdLf)
  where vsCdLf = S.filter isFloatingGVar vsCdL
\end{code}

\subsubsection{Pairwise Discharging (D:D)}

\begin{eqnarray*}
   D_G \disj V \discharges D_L \disj V
   & = & \true
         \quad\cond{D_L \subseteq D_G}\quad (D_L\setminus D_G) \disj V
\end{eqnarray*}
Edge case: \m{D_G = \emptyset} means no change to law s.c.
\begin{code}
vspDischarge obsv (VSDisj gv vsDG) predL@(VSDisj _ vsDL)
  | S.null vsDG                  =  return predL
  | vsDL `S.isSubsetOf` vsDG     =  return VSTrueP 
  | otherwise                    =  return $ VSDisj gv (vsDL S.\\ vsDG)
\end{code}

\subsubsection{Pairwise Discharging (C:D)}

\begin{eqnarray*}
   C_G \supseteq V \discharges D_L \disj V
   & = & \true, \quad \IF \quad C_G \disj D_L
\\ & = & \false, \quad \IF \quad C_G \subseteq D_L \land isObsVar(V)
\\ & = & (D_L \cap C_G)\disj V, \quad \textbf{otherwise}
\end{eqnarray*}
Edge cases:
\newline
  \m{C_G = \emptyset} discharges \m{D_L \disj V} 
  because it implies \m{\fv(V)=\emptyset}
\newline
  If \m{V} is a term variable, 
  then it is possible that \m{fv(V)=\emptyset},
  in which case the fact that \m{C_G \subseteq D_L} is irrelevant.
\begin{code}
vspDischarge obsv (VSSub gv vsCG) predL@(VSDisj _ vsDL)
  | S.null vsCG                               =  return predL
  | vsCG `S.disjoint` vsDL                    =  return VSTrueP 
  | vsCG `S.isSubsetOf` vsDL && isObsGVar gv  =  fail "discharge CD false"
  | otherwise            =  return $ VSDisj gv  (vsDL `S.intersection` vsCG)
vspDischarge obsv (VSSubD gv vsCdG) predL@(VSDisj _ vsDL)
  | S.null vsCdG                               =  return predL
  | vsCdG `S.disjoint` vsDL                    =  return VSTrueP 
  | vsCdG `S.isSubsetOf` vsDL && isObsGVar gv  =  fail "discharge CdD false"
  | otherwise            =  return $ VSDisj gv  (vsDL `S.intersection` vsCdG)
\end{code}

\subsubsection{Pairwise Discharging (D:C)}

\begin{eqnarray*}
   D_G \disj V \discharges C_L \supseteq V
   & = & \false
         \quad\cond{C_L \subseteq D_G \land isObsVar(V)}\quad
         (C_L \setminus D_G) \supseteq V
\end{eqnarray*}
Edge case: \m{D_G = \emptyset} means no change to law s.c.
\begin{code}
vspDischarge obsv (VSDisj gv vsDG) predL@(VSSub _ vsCL)
  | S.null vsDG                  =  return predL
  | vsCL `S.isSubsetOf` vsDG && isObsGVar gv= fail "discharge DC false"
  | otherwise  =  return $ VSSub gv (vsCL S.\\ vsDG)
vspDischarge obsv (VSDisj gv vsDG) predL@(VSSubD _ vsCdL)
  | S.null vsDG                  =  return predL
  | vsCdL `S.isSubsetOf` vsDG && isObsGVar gv= fail "discharge DCd false"
  | otherwise  =  return $ VSSubD gv (vsCdL S.\\ vsDG)
\end{code}

We have a catch-all here:
\begin{code}
vspDischarge obsv vspG vspL 
  = fail ("vspDischarge NYfI:\n"++show vspG++" => "++show vspL)
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
               => VarSet -> VarSet -> VarSet -> [VSetPred] 
               -> m SideCond
freshDischarge obsv anteFvs cnsqFvs vsp
  = do vsp' <- freshDischarge' obsv anteFvs vsp
       return (SCD vsp'  (cnsqFvs S.\\ anteFvs) )
\end{code}

\begin{code}
freshDischarge' :: MonadFail m 
                => VarSet -> VarSet -> [VSetPred] 
                -> m [VSetPred]
freshDischarge' obsv anteFvs [] = return []
freshDischarge' obsv anteFvs (vsp:vsps)
  = do ascl   <- freshTVarDischarge obsv anteFvs vsp
       vsps' <- freshDischarge'    obsv anteFvs vsps
       return (ascl++vsps')
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
                   => VarSet -> VarSet -> VSetPred 
                   -> m [VSetPred]
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
freshTVarDischarge obsv gF (VSDisj gv vsD) = do
  let vsD' = (vsD S.\\ gF)
  if S.null vsD' then return []
                 else return [VSDisj gv vsD']
freshTVarDischarge obsv gF (VSSub  gv vsC) = do
  let vsC' = (vsC S.\\ gF)
  if S.null vsC' then fail "fresh-var s.c. discharge failed (C)"
                 else return [VSSub gv vsC']
freshTVarDischarge obsv gF (VSSubD gv vsCd)
  = if gv `S.member` obsv then do
      let vsCd' =  (vsCd S.\\ gF)
      if S.null vsCd' then fail "fresh-var s.c. discharge failed (Cd)"
                      else return [VSSubD gv vsCd']
    else return []
freshTVarDischarge _ _ _ = return []
\end{code}
  % | vsp' == vspTrue gv  =  return []
  % | otherwise  =  return [vsp']
  % where
  %   nvsgF = The gF
  %   nvsD' = nvsD `ndiff` nvsgF
  %   nvsC' = nvsC `ndiff` nvsgF
  %   nvsCd' = if gv `S.member` obsv
  %            then nvsCd `ndiff` nvsgF
  %            else NA
  %   vsp' = case mkVSC gv nvsD' nvsC' nvsCd' of
  %            Nothinh
  %            Nothing   ->  vspTrue gv
  %            Just vsp  ->  vsp


\newpage
\section{Check for Floating Conditions}

When discharge at match application
results in a residual side-condition (not trivially true)
then we need to check that \emph{all} the term variable side-conditions in that residual
mention variables that are marked as ``floating''.
Only these can possibly be instantiated to satisfy the residual side-condition.
\begin{code}
isFloatingVSC :: VSetPred -> Bool
isFloatingVSC (VSDisj gv vset) = isFloatingGVar gv || hasFloating vset
isFloatingVSC (VSSub  gv vset) = isFloatingGVar gv || hasFloating vset
isFloatingVSC (VSSubD gv vset) = isFloatingGVar gv || hasFloating vset
isFloatingVSC vsp = True -- true or false
hasFloating :: VarSet -> Bool
hasFloating vs = any isFloatingGVar $ S.toList vs
\end{code}
% One exception to this, during law matching,
% is that coverage may reduce to the empty set
% because unbound variables given a temporary binding
% to a ``?'' variable (\texttt{bindFloating})
% will not cancel out other variables that they should be able to do,
% if instantiated properly.
% \begin{code}
% tolerateAutoOrNull :: VarSet -> VSetPred -> Bool
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
addFreshVars freshlynew (SCD vsps freshv) 
  = SCD vsps (freshlynew `S.union` freshv)

onlyFreshSC :: SideCond -> Bool
onlyFreshSC (SCD vsps fvars) = null vsps
\end{code}


\newpage
\section{Building side-conditions.}

Simple side-condition builders.

$\lst v \disj \fv(T)$
\begin{code}
notin :: VarList -> GenVar -> SideCond
vl `notin` tV  =  SCD [ tV `disjfrom`(S.fromList vl) ]  S.empty 
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> GenVar -> SideCond
vl `covers` tV  =  SCD [ tV `coveredby` (S.fromList vl) ] S.empty 
\end{code}

$\lst v \supseteq_a \fv(T)$
\begin{code}
dyncover :: VarList -> GenVar -> SideCond
vl `dyncover` tV  =  SCD [ tV `dyncovered` (S.fromList vl) ] S.empty 
\end{code}

$u,v,\dots \textbf{fresh.}$
\begin{code}
fresh :: VarSet -> SideCond
fresh fvs = SCD [] fvs
\end{code}

\newpage
\section{Side-condition Queries and Operations}

First, some simple queries to find term variable side-conditions of interest.
We start by checking if a variable is mentioned.
\begin{code}
findGenVarInSC :: MonadFail m => GenVar -> SideCond -> m VSetPred
findGenVarInSC gv (SCD vsps _ )  =  findGV gv vsps

findGV _ [] = fail "findGenVarInSC: not in any term variable side-condition"
findGV gv (vsp:vsps) 
  = case termVar vsp of
      Just gv' | gv== gv'  ->  return vsp
      _                    ->  findGV gv vsps
\end{code}

We then look at returning all mentions of a variable:
\begin{code}
findAllGenVar :: GenVar -> SideCond -> [VSetPred]
findAllGenVar gv (SCD vsps _)  =  findAGV gv [] vsps

findAGV _ scsa []  =  reverse scsa
findAGV gv scsa (vsp:vsps) = []
--  | gv == termVar vsp  =  findAGV gv (vsp:scsa) vsps
-- | otherwise          =  findAGV gv scsa       vsps
\end{code}

We sometimes want mentions for a specific condition type:

For disjointness we look for precisely the given general variable.
\begin{code}
findDisjointGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findDisjointGenVar gv (SCD vsps _) = findDGV gv vsps

findDGV gv []         =  fail ("Disjoint "++show gv ++ " not found")
findDGV gv (VSDisj gv' vsD : vsps)
  | gv == gv' && not (S.null vsD)  =  return vsD
findDGV gv (_:vsps)                =  findDGV gv vsps
\end{code}

For regular coverage we look for precisely the given general variable,
while for dynamic coverage we ignore differences in temporality.
\begin{code}
findCoveredGenVar :: MonadFail m => GenVar -> SideCond -> m VarSet
findCoveredGenVar gv (SCD vsps _) = findCGV gv vsps

findCGV gv []           =  fail ("Covered "++show gv ++ " not found")
findCGV gv (VSSub gv' vsC : vsps)
  | gv == gv'           =  return vsC
findCGV gv (VSSubD gv' vsCd : vsps)
  | gv == gv'           =  return vsCd
findCGV gv (_:vsps)     =  findCGV gv vsps
\end{code}

For dynamic coverage we don't care about temporality,
but do report what temporality was found.
\begin{code}
findDynCvrdGenVar :: MonadFail m => GenVar -> SideCond -> m ( VarSet, VarWhen )
findDynCvrdGenVar gv (SCD vsps _) = findDCGV gv vsps

findDCGV gv []         =  fail ("DynCovered "++show gv ++ " not found")
findDCGV gv (VSSubD gv' vsCd : vsps)
  = case gv `dynGVarEq` gv' of
      Just vw'  ->  return (vsCd, vw')
      Nothing   ->  findDCGV gv vsps
\end{code}

We have a catch-all :
\begin{code}
mentionedBy :: MonadFail m 
            => GenVar -> [VSetPred] -> m ( VSetPred, Maybe VarWhen)
gv `mentionedBy` []  =  fail ("variable "++show gv++" not mentioned")
gv `mentionedBy` (vsp@(VSSubD gv' vsCd):vsps)
  | gv == gv'       =  return ( vsp, Nothing )
  | otherwise
      = case gv `dynGVarEq` gv' of
          Just vw'  ->  return ( vsp, Just vw')
          _         ->  gv `mentionedBy` vsps
gv `mentionedBy` (vsp:vsps)
  = case vPredVar vsp of
      Nothing -> gv `mentionedBy` vsps
      Just gv' | gv == gv' -> return ( vsp, Nothing )
               | otherwise -> gv `mentionedBy` vsps
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


tstFalse = VSFalseP
tstTrue  = VSTrueP

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

mkVSC _ _ _ _ = Nothing
tst_scChkDisjoint
 = testGroup "disjfrom  (no known vars)"
    [ --testCase "Definitely True: ls   `disj` ls'"
      -- ( mkVSC (StdVar vls) (StdVar vls') NA NA 
      --   @?= Just Nothing )
    --, testCase "Definitely True: ls_1 `disj` ls"
      -- ( mkVSC (StdVar vls1) (StdVar vls) NA NA 
      --   @?= Just Nothing )
      testCase "gv_a `disjoint` empty is True"
       ( (disjfrom  gv_a S.empty) @?= tstTrue )
    , testCase "v_e `disjoint` empty is True"
       ( (disjfrom  v_e S.empty) @?= tstTrue )
    , testCase "gv_a `disjoint` {gv_a} is False"
       ( (disjfrom  gv_a $ S.singleton gv_a) @?= tstFalse )
    , testCase "gv_a `disjoint` {gv_b} is True"
       ( (disjfrom  gv_a $ S.singleton gv_b) @?= tstTrue )
    , testCase "v_e `disjoint` {v_e} stands"
       ( (disjfrom  v_e $ S.singleton v_e)
         @?= (disjfrom  v_e $ S.singleton v_e) )
    , testCase "v_e `disjoint` {v_f} stands"
       ( (disjfrom  v_e $ S.singleton v_f)
         @?= (disjfrom  v_e $ S.singleton v_f) )
    , testCase "v_e `disjoint` {gv_a} stands"
       ( (disjfrom  v_e $ S.singleton gv_a)
         @?= (disjfrom  v_e $ S.singleton gv_a) )
    , testCase "gv_a `disjoint` {v_f} stands"
       ( (disjfrom  gv_a $ S.singleton v_f)
         @?= (disjfrom  gv_a $ S.singleton v_f) )
    , testCase "gv_a `disjoint` {gv_b,v_f} stands without gv_b"
       ( (disjfrom  gv_a $ S.fromList [gv_b,v_f])
         @?= (disjfrom  gv_a $ S.fromList [v_f]) )
    ]

tst_scChkCovers
 = testGroup "coveredby  (no known vars)"
    [ testCase "gv_a `coveredby` empty is False"
       ( (coveredby  gv_a S.empty) @?= tstFalse )
    , testCase "v_e `coveredby` empty stands"
       ( (coveredby  v_e S.empty)
         @?= (coveredby  v_e S.empty) )
    , testCase "gv_a `coveredby` {gv_a} is True"
       ( (coveredby  gv_a $ S.singleton gv_a) @?= tstTrue )
    , testCase "gv_a `coveredby` {gv_b} is False"
       ( (coveredby  gv_a $ S.singleton gv_b) @?= tstFalse )
    , testCase "v_e `coveredby` {v_e} is True"
       ( (coveredby  v_e $ S.singleton v_e) @?= tstTrue )
    , testCase "v_e `coveredby` {v_f} stands"
       ( (coveredby  v_e $ S.singleton v_f)
         @?= (coveredby  v_e $ S.singleton v_f) )
    , testCase "v_e `coveredby` {gv_a} stands"
       ( (coveredby  v_e $ S.singleton gv_a)
         @?= (coveredby  v_e $ S.singleton gv_a) )
    , testCase "gv_a `coveredby` {v_f} stands"
       ( (coveredby  gv_a $ S.singleton v_f)
         @?= (coveredby  gv_a $ S.singleton v_f) )
    , testCase "gv_a `coveredby` {gv_b,v_f} stands"
       ( (coveredby  gv_a $ S.fromList [gv_b,v_f])
         @?= (coveredby  gv_a $ S.fromList [v_f]) )
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
     , testCase "merge gv_a `disjoint` empty  into [vsp(gv_b)] is [vsp(gv_b)]"
        ( mrgVarConds (disjfrom  gv_a S.empty) [vsp1] @?= Just [vsp1] )
     , testCase "merge gv_a `disjoint` {gv_a} into [vsp(gv_b)] is False"
        ( mrgVarConds (disjfrom  gv_a $ S.singleton gv_a) [vsp1] @?= Nothing )
     , testCase
        "merge v_e `coveredby` {v_f}  into [vsp(gv_b)] is [vsp(gv_b),itself]"
        ( mrgVarConds (coveredby  v_e $ S.singleton v_f) [vsp1]
          @?= Just [vsp1,coveredby  v_e $ S.singleton v_f] )
     ]

vsp1 = (coveredby  gv_b $ S.fromList [gv_b,v_f])
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
