\chapter{Matching}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017-22

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Matching
( match, itop
  -- below exported for testing
, typeMatch, termMatch, tsMatch
, tvMatch, tkvMatch
, vMatch, bvMatch
, vsMatch, vlMatch
, sMatch
) where
import Data.Maybe (isJust,fromJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad
import Data.List

import Utilities
import Control
import LexBase
import Variables
import Types
import AST
import SideCond
import FreeVars
import VarData
import Typing
import Binding


import Debugger
\end{code}

\section{Matching Principles}

We want to match a candidate term ($C$) against a pattern term ($P$)
in some context ($\Gamma$),
to obtain a binding ($\beta$), if successful,
of pattern variables to appropriate term components.
$$
\Gamma \vdash C :: P  \leadsto \beta
$$
The context has two components,
the first ($\kappa$) being the known variables,
and the second ($B$) keeping track of bound variables.
We need to track bound variables for both
the candidate ($B_C$)
and pattern ($B_P$)
$$
\kappa;(B_C,B_P) \vdash C :: P  \leadsto \beta
$$
The use-case that is most common in the planned use for matching
is where we want to match a single candidate against many patterns.
We expect most such matches to fail,
and so we want to design our algorithms
to discover failure as fast as possible.
This means doing top-level structural matching first,
and only then trying the more complex and tricky matching
of variable lists and sets.

The idea is that we attempt to construct a binding on-the-fly,
doing matching on one sub-component at a time,
passing the partial binding result along and attempting to add new bindings
directly into it.
$$
\kappa;\beta;(B_C,B_P) \vdash C :: P \leadsto \beta'
$$
We also posit a binary partial operator ($\uplus$) that merges two bindings
as long as overlapping entries agree,
so the assertion $\beta = \beta_1 \uplus \beta_2$ is true only if all overlapping entries in the $\beta_i$ agree,
and $\beta$ corresponds to their union.

We are not normally interested in the reason why a match fails,
so will generally use the \texttt{Maybe} type constructor.
However we code for a general monad with meaningful \texttt{fail} messages
to make it easier to debug or test.
We also need to support the idea that some patterns may match a given
candidate in more than one way,
so we would like to return a list of bindings,
leading us to adopt the \texttt{MonadPlus} class.
$$
\kappa;\beta;(B_C,B_P) \vdash C :: P
\leadsto \langle \beta'_1 , \dots , \beta'_n \rangle
$$
Each of the $\beta'_i$
has the general form $\beta'_{i1} \uplus \dots \uplus \beta'_{ik_i}$,
and a rule applies provided at least one of the $\beta'_i$ is defined.
We write $\langle\beta\rangle$ as $\beta$
and in most rules we omit irrelevant parts of the context.
\newpage
\section{Haskell Types for Matching}

We introduce some type and value synonyms,
to make type-signatures more informative.
\begin{code}
type Pattern = Term
type Candidate = Term
type BVS = Set GenVar
type PBVS = BVS
type CBVS = BVS

noBVS = S.empty
\end{code}

We will want to add in sets and lists of variables
into the bound-variable sets.
\begin{code}
addBoundVarSet :: VarSet -> BVS -> BVS
vs `addBoundVarSet` bvs  =  vs `S.union` bvs

addBoundVarList :: VarList -> BVS -> BVS
vl `addBoundVarList` bvs  =  (S.fromList vl) `S.union` bvs
\end{code}

\section{Top-level Matching}

At the top-level we have the known-variable information
in the form of a sequence $\kappa s$ of known variable tables,
and the pattern and candidate terms,
and we hope to get at least one binding.
We also need a canonical type-variable mapping,
obtained from type inference.
We initialise the bound-variable sets to empty ($\emptyset$)
and the bindings already obtained to the null map ($\theta$).
$$
\inferrule
   {\kappa s;\theta;(\emptyset,\emptyset) \vdash C :: P \leadsto \beta s}
   {\kappa s \vdash C :: P \leadsto \beta s}
   \quad
   \texttt{match}
$$
\begin{code}
match :: (MonadPlus mp, MonadFail mp) 
      => [VarTable]-> TypCmp
      -> Candidate -> Pattern -> mp Binding
match vts fits cand patn  
  =  termMatch vts fits emptyBinding noBVS noBVS cand patn
\end{code}

\newpage
\section{Type Matching}


\begin{code}
type TVCmp = Identifier -> Identifier -> Bool
typeMatch :: MonadFail m 
          => (TypCmp,TVCmp) -> Binding -> Type -> Type
          -> m Binding
typeMatch _ bind typC ArbType       =  return bind 

typeMatch (fits,vfits) bind typC@(TypeVar iC) (TypeVar iP)
  | iC `vfits` iP  =  bindTypeVarToType fits iP typC bind
typeMatch (fits,_) bind typC (TypeVar iP) 
                   =  bindTypeVarToType fits iP typC bind
-- !! will this work?
typeMatch (fits,_) bind (TypeVar iC) typP 
                   =  bindTypeVarToType fits iC typP bind

typeMatch (fits,vfits) bind typC@(TypeCons iC tsC) (TypeCons iP tsP)
  | iC `vfits` iP = do
    bindI <- bindTypeVarToType fits iP (TypeVar iC) bind
    typesMatch (fits,vfits) bindI tsC tsP

typeMatch (fits,vfits) bind typC@(AlgType iC fsC) (AlgType iP fsP)
  | iC `vfits` iP && fsC == fsP   =  bindTypeVarToType fits iP typC bind
  -- temporary: we should typeMatch fsC!!i :: fsP!!i

typeMatch (fits,vfits) bind typC@(FunType tdC trC) (FunType tdP trP) = do
  bindD <- typeMatch (fits,vfits) bind tdC tdP
  typeMatch (fits,vfits) bindD trC trP

typeMatch _ bind _ BottomType = return bind  

-- `vfits` not relevant here
typeMatch (fits,_) bind typC@(GivenType iC) (GivenType iP)
  | iC == iP  =  bindTypeVarToType fits iP typC bind

-- typeMatch (fits,_) bind typC typP@(GivenType iP)
--   | typC `fits` typP  =  bindTypeVarToType fits iP typC bind

typeMatch (fits,vfits) bind typC typP 
  = fail $ unlines [ "typeMatch: distinct types"
                   , "typC = " ++ show typC
                   , "typP = " ++ show typP ]

typesMatch (fits,vfits) bind [] [] = return bind
typesMatch (fits,vfits) bind (tC:tsC) (tP:tsP) = do
  bindH <- typeMatch (fits,vfits) bind tC tP
  typesMatch (fits,vfits) bindH tsC tsP
typesMatch (fits,vfits) bind tsC tsP = fail $ unlines
  [ "typesMatch: length difference "++show (length tsP - length tsC)]
\end{code}

\newpage
\section{Term Matching}

\begin{code}
termMatch, termMatch' :: (MonadPlus mp, MonadFail mp) 
                => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
                -> Candidate -> Pattern -> mp Binding
\end{code}

We note that the \texttt{Type} of pattern and candidate must agree,
in that the candidate is a subtype of the pattern.
Note that predicate-type $t$ is the same as expression-type $t\fun\Bool$.
\begin{code}
termMatch vts fits bind cbvs pbvs tC tP
  = let typC = termtype tC ; typP = termtype tP
    in do
      bindT <- typeMatch (fits,vfits) bind typC typP
      termMatch' vts fits bindT cbvs pbvs tC tP
  where vfits iC iP = fits (TypeVar iC) (TypeVar iP)
\end{code} 



Term-matching is defined inductively over the pattern type.
We also introduce a special identifier (\itop) used when 
a constructor term matches against an iteration.
\begin{code}
itop = jId "_itop"
\end{code}

\subsection{Value Term-Pattern (\texttt{Val})}

Values only match themselves, and add no new bindings.

$$
\inferrule
   {{\kk k}_C = {\kk k}_P}
   {\beta \vdash {\kk k}_C :: {\kk k}_P \leadsto \beta}
   \quad
   \texttt{termMatch Val}
$$

\begin{code}
termMatch' _ _ bind _ _ kC@(Val _ _) kP@(Val _ _)
 | kC == kP  =  return bind
\end{code}

\subsection{Variable Term-Pattern (\texttt{Var})}

Here we have 
Variable matching is complicated, so we farm it out,
as long as \texttt{Type}s match.
Here we have an issue if \h{tC} is a \h{Bnd},
in which case we expect the type of its \emph{body} 
to fit with the type of \h{vP}.

$$
\inferrule
   {type(t_C) \cong type(v_P)
    \and
    \beta \vdash \bb{n_C}{vs_C}{t_C} :: v_P \leadsto \beta'}
   {\beta \vdash \bb{n_C}{vs_C}{t_C}  :: {\vv v}_P \leadsto \beta'}
   \quad
   \texttt{termMatch Bind vs Var}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs tC@(Bnd ttC nC vsC tbodyC) (Var ttP vP)
  | termtype tbodyC `fits` ttP  =  tvMatch vts fits bind cbvs pbvs tC ttP vP
\end{code}

$$
\inferrule
   {\beta \vdash t_C :: v_P \leadsto \beta'}
   {\beta \vdash t_C :: {\vv v}_P \leadsto \beta'}
   \quad
   \texttt{termMatch non-Bind vs Var}
$$

\begin{code}
termMatch' vts fits bind cbvs pbvs tC (Var ttP vP)
  | termtype tC `fits` ttP  =  tvMatch vts fits bind cbvs pbvs tC ttP vP
\end{code}

\newpage
\subsection{Constructor Term-Pattern (\texttt{Cons})}

Constructors match if they have the same kind,
their names match (as static observation variables)
and the term-lists are of the same length and corresponding terms match.

$$
\inferrule
   { \beta \vdash n_C :: n_P \leadsto \beta_0
     \and
     \beta \vdash t_{C_i} :: t_{P_i} \leadsto \beta_i
   }
   {\beta \vdash \cc{n_C}{ts_C} :: \cc{n_P}{ts_P}
    \leadsto
    \uplus_{i \in 0\dots n}\{\beta_i\}}
   \quad
   \texttt{termMatch Cons}
$$

Here $ts_X = \langle t_{X_1}, t_{X_2}, \dots t_{X_n} \rangle$.
\begin{code}
termMatch' vts fits bind cbvs pbvs (Cons ttC sbC nC tsC) (Cons ttP sbP nP tsP)
 | ttC `fits` ttP && sbC == sbP
   =  do bind0 <- consBind vts fits bind cbvs pbvs ttC nC nP
         tsMatch vts fits bind0 cbvs pbvs tsC tsP
\end{code}


Constructor patterns with variable-only sub-terms
can also match against Iterations.
Here we have an issue where we have nothing in the constructor
that matches the outer name of the Iterator, 
and the replacement term has an occurrence of the iterator.
We use the special (meta-)variable \itop\ to record this.

Single case:
$$
\inferrule
  {ni_C = n_P \and ts_P[i] = \vv v_i}
  {\beta \vdash \ii{na_C}{ni_C}{lvs_C} :: \cc {n_P}{ts_P} 
     \leadsto
     \beta 
     \uplus 
     \{ \itop \mapsto na_C \}
     \uplus
     \{ ts_P[i] \mapsto lvs_C[i] \}_{i \in 1\dots\#lvs_C}}
  \quad\texttt{termMatch Single-Iter}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs (Iter ttC saC naC siC niC lvsC) (Cons ttP sbP nP tsP)
  | ttC `fits` ttP && niC == nP && siC == sbP
    =  do bind0 <- consBind vts fits bind cbvs pbvs ttC niC nP
          -- ignore above Cons bind for now
          bind1 <- consBind vts fits bind cbvs pbvs ttC naC itop
          -- tsMatch vts fits bind0 cbvs pbvs tsC tsP
          iterVarsMatch bind1 tsP lvsC  
  where
    iterVarsMatch bind [] [] = return bind
    iterVarsMatch bind (Var ttP vP:tsP) (lvC:lvsC)
      = do bind' <- bindVarToLVar vP lvC bind
           iterVarsMatch bind' tsP lvsC
    iterVarsMatch _ _ _ = fail "Single-Iter: non-Var term or length mismatch"
\end{code}


$$
\inferrule
   {ni_C = ni_P \and \#\seqof{t_I} = \#lvs_P}
   { \beta \vdash ni_C\seqof{t_I} :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus \{lvs_P[i] \mapsto t_I[i]\}_{i \in 1\dots\#lvs_P}
   }
   \quad
   \texttt{termMatch Iter-Single}
$$


General case:
$$
\inferrule
  {this}
  {\beta \vdash \ii{na_C}{ni_C}{lvs_C} :: \cc {na_P}{ts_P}
     \leadsto
     \beta \uplus (\frown) \beta_j}
  \quad
  \texttt{termMatch Cons-Iter}
$$

$$
\inferrule
   {na_C = na_P \and ni_C = ni_P
   \and
   j \in 1 \dots\#\seqof{t_C} \and i \in 1 \dots\#lvs_P
   \\\\
   {t_C}_j = ni_C\seqof{t_I}_j \implies \#(\seqof{t_{I}}[j]) = \#lvs_P
   \\\\
   {t_C}_j = ni_C\seqof{t_I}_j
   \implies
   \beta_j = \{lvs_P[i] \mapsto \seqof{t_C[i]}_j\}
   \\\\
     {t_C}_j = \ii{na_P}{ni_P}{lvs_C} \implies \#lvs_C = \#lvs_P
   \\\\
     {t_C}_j = \ii{na_P}{ni_P}{lvs_C}
     \implies
     lvs_C[i] = lvs_P[i]\less V
     \land
     \beta_j = \{lvs_P[i] \mapsto lvs_C[i]\}
   }
   { \beta \vdash na_C({t_C}_j) :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus (\frown) \beta_j
   }
   \quad
   \texttt{termMatch Iter-Cons}
$$
We use $(\frown)$ to denote the ``striping'' of the mappings,
e.g.
$$
  lvsp[i] \mapsto \seqof{t_C[i]}_1 \frown \dots \frown lvs_C[\#lvs_P]
$$


\newpage
\subsection{Binding Term-Pattern (\texttt{Bnd})}

We first start with the obvious rule that tries to match
a candidate binding against a candidate pattern:
$$
\inferrule
   {n_C = n_P
    \and
    \beta;(B_C\cup vs_C,B_P\cup vs_P) \vdash t_C :: t_P \leadsto \beta'_t
    \and
    \beta \vdash vs_C :: vs_P \leadsto \beta'_{vs}
   }
   { \beta;(B_C,B_P) \vdash \bb{n_C}{vs_C}{t_C} :: \bb{n_P}{vs_P}{t_P}
     \leadsto
     \beta \uplus \beta'_t \uplus \beta'_{vs}
   }
   \quad
   \texttt{termMatch Binding}
$$
Remember, the type of $\forall \lst x \bullet P$ is the type of $P$:
\begin{code}
termMatch' vts fits bind cbvs pbvs (Bnd ttC nC vsC tC) (Bnd ttP nP vsP tP)
  | (termtype tC) `fits` (termtype tP) && nC == nP
    =  do let cbvs' = vsC `addBoundVarSet` cbvs
          let pbvs' = vsP `addBoundVarSet` pbvs
          bindT  <-  termMatch vts fits bind cbvs' pbvs' tC tP
          vsMatch vts fits bindT cbvs' pbvs' vsC vsP
\end{code}

However, we also have the case when the pattern binding
has quantifier variables that are are all unknown list-variables.
In this case, they could all be bound to empty variable-sets,
and then we just try to match its body, with that binding,
to any candidate term.
$$
\inferrule
   {\lst{vs}_P \not{\!\cap}~ \kappa s
   \and
   \beta_{vs} = \{ \lst{vs}_P \mapsto \emptyset \}
   \and
   \kappa s;\beta\uplus \beta_{vs};(B_C\cup vs_C,B_P\cup vs_P) \vdash t_C :: t_P \leadsto \beta'_t
   }
   { \kappa s;\beta;(B_C,B_P) \vdash t_C :: \bb{n_P}{\lst{vs}_P}{t_P}
     \leadsto
     \beta \uplus \beta'_t \uplus \beta'_{vs}
   }
   \quad
   \texttt{termMatch Binding0}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs tC (Bnd ttP nP vsP tP)
  | all (gVarIsUnknownLVar vts) vlP
    =  do bind' <- bindLVarsToEmpty bind $ listVarsOf vlP
          let pbvs' = vsP `addBoundVarSet` pbvs
          termMatch vts fits bind' cbvs pbvs' tC tP
  where vlP = S.toList vsP
\end{code}


\subsection{Lambda Term-Pattern (\texttt{Lam})}

$$
\inferrule
   {n_C = n_P
    \and
    \beta;(B_C\cup vl_C,B_P\cup vl_P) \vdash t_C :: t_P \leadsto \beta'_t
    \and
    \beta \vdash vl_C :: vl_P \leadsto \beta'_{vl}
   }
   { \beta;(B_C,B_P) \vdash \ll{n_C}{vl_C}{t_C} :: \ll{n_P}{vl_P}{t_P}
     \leadsto
     \beta \uplus \beta'_t \uplus \beta'_{vl}
   }
   \quad
   \texttt{termMatch Lambda}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs (Lam ttC nC vlC tC) (Lam ttP nP vlP tP)
  | ttC `fits` ttP && nC == nP
    =  do let cbvs' = vlC `addBoundVarList` cbvs
          let pbvs' = vlP `addBoundVarList` pbvs
          bindT  <-  termMatch vts fits bind cbvs' pbvs' tC tP
          vlMatch vts fits bindT cbvs' pbvs' vlC vlP
\end{code}
We also have special handling here for when we have only unknown list-variables:
$$
\inferrule
   {\lst{vl}_P \not{\!\cap}~ \kappa s
   \and
   \beta_{vl} = \{ \lst{vl}_P \mapsto \nil \}
   \and
   \kappa s;\beta\uplus \beta_{vl};(B_C\cup vl_C,B_P\cup vl_P) \vdash t_C :: t_P \leadsto \beta'_t
   }
   { \kappa s;\beta;(B_C,B_P) \vdash t_C :: \ll{n_P}{\lst{vl}_P}{t_P}
     \leadsto
     \beta \uplus \beta'_t \uplus \beta'_{vl}
   }
   \quad
   \texttt{termMatch Lambda0}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs tC (Lam ttP nP vlP tP)
  | all (gVarIsUnknownLVar vts) vlP
    =  do bind' <- bindLVarsToEmpty bind $ listVarsOf vlP
          let pbvs' = vlP `addBoundVarList` pbvs
          termMatch vts fits bind' cbvs pbvs' tC tP
\end{code}

\newpage
\subsection{Closure Term-Pattern (\texttt{Cls})}

$$
\inferrule
   {n_C = n_P
    \and
    \beta;(\fv(t_C),\fv(t_P)) \vdash t_C :: t_P \leadsto \beta'
   }
   { \beta \vdash \xx{n_C}{t_C} :: \xx{n_P}{t_P}
     \leadsto
     \beta \uplus \beta'
   }
   \quad
   \texttt{termMatch Closure}
$$
Note that here we only close w.r.t. free \emph{observational} variables.
\begin{code}
termMatch' vts fits bind cbvs pbvs (Cls nC tC) (Cls nP tP)
  | nC == nP  =  termMatch vts fits bind cbvs' pbvs' tC tP
  where
    cbvs' = S.filter isObsGVar $ theFreeVars $ freeVars scTrue tC -- safe?
    pbvs' = S.filter isObsGVar $ theFreeVars $ freeVars scTrue tP -- safe?
\end{code}

\subsection{Substitution Term-Pattern (\texttt{Sub})}

$$
\inferrule
   {n_C = n_P
    \and
    \beta \vdash t_C :: t_P \leadsto \beta'_t
    \and
    \beta \vdash \sigma_C :: \sigma_P \leadsto \beta'_\sigma
   }
   { \beta \vdash t_C\sigma_C :: t_P\sigma_P
     \leadsto
     \beta \uplus \beta'_t \uplus \beta'_\sigma
   }
   \quad
   \texttt{termMatch Subst}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs (Sub ttC tC subC) (Sub ttP tP subP)
  | ttC `fits` ttP 
    = do  bindT  <-  termMatch vts fits bind cbvs pbvs tC tP
          sMatch vts fits bindT cbvs pbvs subC subP
\end{code}


\subsection{Iterated Term-Pattern (\texttt{Iter})}

The first case is simply where the candidate is itself an iteration,
which is essentially a structural match, even over the list-variables.
$$
\inferrule
   {na_C = na_P \and ni_C = ni_P
    \and \#lvs_C = \#lvs_P
   }
   { \beta \vdash \ii{na_C}{ni_C}{lvs_C} :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus \{lvs_P[i] \mapsto lvs_C[i]\}_{i \in 1\dots\#lvs_P}
   }
   \quad
   \texttt{termMatch Iter-Self}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs (Iter ttC saC naC siC niC lvsC)
                           (Iter ttP saP naP siP niP lvsP)
  | ttP == ttC && naC == naP && niC == niP
               && saC == saP && siC == siP
               && length lvsP == length lvsC
               =  do bind0 <- consBind vts fits bind  cbvs pbvs ttC naC naP
                     bind1 <- consBind vts fits bind0 cbvs pbvs ttC niC niP
                     -- iibind bind1 $ zip lvsP lvsC
                     iibind bind $ zip lvsP lvsC -- no cons just now
  | otherwise  =  fail "termMatch: incompatible Iter."
  where
    iibind bind [] = return bind
    iibind bind ((lvP,lvC):rest)
      = do bind' <- bindLVarToVList lvP [LstVar lvC] bind
           iibind bind' rest
\end{code}

\newpage

The next case is when the candidate is an expansion of length one,
without the application of the top-level operator $na$.
$$
\inferrule
   {ni_C = ni_P \and \#\seqof{t_I} = \#lvs_P}
   { \beta \vdash ni_C\seqof{t_I} :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus \{lvs_P[i] \mapsto t_I[i]\}_{i \in 1\dots\#lvs_P}
   }
   \quad
   \texttt{termMatch Iter-Single}
$$
\begin{code}
termMatch' vts fits bind cbvs pbvs tC@(Cons ttC siC niC tsC)
                           tP@(Iter ttP saP naP siP niP lvsP)
  | ttP == ttC && niC == niP && siC == siP
               = do bind0 <- consBind vts fits bind  cbvs pbvs ttC naP naP
                    bind1 <- consBind vts fits bind0 cbvs pbvs ttC niC niP
                    -- iterLVarsMatch bind1 lvsP tsC
                    iterLVarsMatch bind lvsP tsC -- no cons for now
  where
    iterLVarsMatch bind [] [] = return bind
    iterLVarsMatch bind (lvP:lvsP) (tC:tsC)
      = do bind' <- bindLVarSubstRepl lvP [Right tC] bind
           iterLVarsMatch bind' lvsP tsC
    iterLVarsMatch bind _ _ = fail "Iter-Single - length mismatch"
\end{code}
A general expansion of an iteration $\ii{na}{ni}{lvs}$
will be a construction of the form $na\seqof{t_j}$
where $t_j$ can either be:
\begin{itemize}
  \item
    a $ni\seqof{vs}$, where $vs$ is a list of term-variables
    of the same length as $lvs$;
  \item
    or, a $\ii{na}{ni}{lvs'}$,
    where each  $\lst v'_i \in lvs'$ is equal to $\lst v_i \less V$,
    for non-empty $V$
\end{itemize}
All the $vs$ and $lvs'$ present should, when aggregated,
be something that the $lvs$ can match.

Consider matching
$x = e \land (\ii{\land}{=}{\lst v \less {x,y},\lst t \less {e,f}}) \land y = f$
with
$\ii{\land}{=}{\lst v,\lst t}$.
We expect the binding
$\{
  \lst v \mapsto \seqof{x,\lst v \less {x,y},y}
  ,
  \lst t \mapsto \seqof{e,\lst t \less {e,f},f}
  \}$.


Matching a general expansion against an iteration:
$$
\inferrule
   {na_C = na_P \and ni_C = ni_P
   \and
   j \in 1 \dots\#\seqof{t_C} \and i \in 1 \dots\#lvs_P
   \\\\
   {t_C}_j = ni_C\seqof{t_I}_j \implies \#(\seqof{t_{I}}[j]) = \#lvs_P
   \\\\
   {t_C}_j = ni_C\seqof{t_I}_j
   \implies
   \beta_j = \{lvs_P[i] \mapsto \seqof{t_C[i]}_j\}
   \\\\
     {t_C}_j = \ii{na_P}{ni_P}{lvs_C} \implies \#lvs_C = \#lvs_P
   \\\\
     {t_C}_j = \ii{na_P}{ni_P}{lvs_C}
     \implies
     lvs_C[i] = lvs_P[i]\less V
     \land
     \beta_j = \{lvs_P[i] \mapsto lvs_C[i]\}
   }
   { \beta \vdash na_C({t_C}_j) :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus (\frown) \beta_j
   }
   \quad
   \texttt{termMatch Iter-Cons}
$$
We use $(\frown)$ to denote the ``striping'' of the mappings,
e.g.
$$
  lvsp[i] \mapsto \seqof{t_C[i]}_1 \frown \dots \frown lvs_C[\#lvs_P]
$$

\newpage

In practice, we note that if a match is going to succeed,
then each ${t_C}_j$ will produce a list of length $\#lvs_P$,
and the transpose of this list will provide the "striped" bindings.

\begin{code}
termMatch' vts fits bind cbvs pbvs tC@(Cons ttC saC naC tsC)
                           tP@(Iter ttP saP naP siP niP lvsP)
  | ttP == ttC && naC == naP && saC == saP
               = do bind0 <- consBind vts fits bind  cbvs pbvs ttC naC naP
                    bind1 <- consBind vts fits bind0 cbvs pbvs ttC niP niP
                    termLists <- sequence $ map (itMatch len lvsP) tsC
                    let bindLists = transpose termLists
                    -- itBind bind1 lvsP bindLists
                    itBind bind lvsP bindLists -- for now
  | otherwise
     = fail $ unlines
         [ "termMatch': General Cons not compatible with Iter."
         , "ttP  = " ++ show ttP
         , "ttC  = " ++ show ttC
         , "naP  = " ++ show naP
         , "naC  = " ++ show naC
         , "saP  = " ++ show saP
         , "saC  = " ++ show saC
         , "tC   = " ++ show tC
         , "tP   = " ++ show tP
         , "bind = " ++ show bind
         ]
  where
    len = length lvsP

    itMatch :: (MonadPlus mp, MonadFail mp) => Int -> [ListVar] -> Term -> mp [LVarOrTerm]
    itMatch len lvsP (Cons ttC siC niC tisC)
      | ttC == ttP && siC == siP && niC == niP && length tisC == len
        =  return $ map Right tisC
    itMatch len lvsP (Iter ttC saC naC siC nic lvsC)
      | ttC == ttP && naC == naP && saC == saP &&
        siC == siP && nic == niP && length lvsC == len
        =  return $ map Left lvsC
    itMatch len lvsP tiC = fail "iterate expansion term does not match"

    -- both lists are the same length
    itBind :: (MonadPlus mp, MonadFail mp) => Binding -> [ListVar] -> [[LVarOrTerm]]
           -> mp Binding
    itBind bind [] []  =  return bind
    itBind bind (lvP:lvsP) (as:aas)
      = do bind' <- bindLVarSubstRepl lvP as bind
           itBind bind' lvsP aas
    itBind _ _ _ = fail "internal error in termMatch' Cons vs. Iter"
\end{code}


% \textbf{The below will be subsumed by above}
% Matching an a full expansion against an iteration:
% $$
% \inferrule
%    {na_C = na_P \and ni_C = ni_P
%    \and
%    \and j \in 1 \dots\#\seqof{t_C}
%    \and
%    \#(\seqof{t_{C}}[j]) = \#lvs_P
%    }
%    { \beta \vdash na_C(ni_C\seqof{t_C}_j) :: \ii{na_P}{ni_P}{lvs_P}
%      \leadsto
%      \beta \uplus \{lvs_P[i] \mapsto \seqof{t_C[i]}_j\}_{i \in 1\dots\#lvs_P}
%    }
%    \quad
%    \texttt{termMatch Iter-Only-Cons}
% $$
% This does not cater for a partial expansion!
% \begin{code}
% termMatch' vts fits bind cbvs pbvs tC@(Cons ttC saC naC tsC)
%                               (Iter ttP saP naP siP niP lvsP)
%   | ttP == ttC && naC == naP && saC == saP && all isNiP tsC
%                = ibind bind $ zip lvsP $ transpose $ map unNiP tsC
%   | otherwise
%      = fail $ unlines
%          [ "termMatch: full Cons not compatible with Iter."
%          , "ttP  = " ++ show ttP
%          , "ttC  = " ++ show ttC
%          , "naP  = " ++ show naP
%          , "naC  = " ++ show naC
%          , "niP  = " ++ show niP
%          , "lvsP = " ++ show lvsP
%          , "tsC  = " ++ show tsC
%          ]
%   where
%     arity = length lvsP
%     isNiP (Cons _ s n ts)  =  n == niP && s == siP && length ts == arity
%     isNiP _                =  False
%     unNiP (Cons _ _ _ ts)  =  ts
%     unNiP _                =  []
%     ibind bind [] = return bind
%     ibind bind ((lvP,tsC):rest)
%       =  do bind' <- bindLVarToTList lvP tsC bind
%             ibind bind' rest
% \end{code}

\subsection{All cases covered}

Any other situation results in failure:
\begin{code}
termMatch' _ _ _ _ _ tC tP
 = fail $ unlines
    [ "termMatch': structural mismatch."
    , "tC = " ++ show tC
    , "tP = " ++ show tP
    ]
\end{code}

\newpage

\subsection{Term Matching Support}

Matching two constructor names.
This is really a match between two identifiers 
that we wrap as static observables:

\begin{code}
consBind vts fits bind cbvs pbvs ttC nC nP
  = vMatch vts fits bind cbvs pbvs ttC vC ttC vP
  where
    vC = Vbl nC ObsV Static
    vP = Vbl nP ObsV Static
\end{code}

\textbf{We should store a mapping from nP to nC as a BindId component,
rather than wrapping it up as a static observation variable.}

\section{Term-List Matching}

A simple zip-like walk along both lists
(precomputing length to abort early).
\begin{code}
tsMatch :: (MonadPlus mp, MonadFail mp)
        => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
        -> [Candidate] -> [Pattern] -> mp Binding
tsMatch vts fits bind cbvs pvbs cts pts
 | length cts /= length pts = fail "tsMatch: length mismatch"
 | otherwise  =  tsMatch' vts fits bind cbvs pvbs cts pts

-- here both lists are the same length
tsMatch' _ _ bind _ _ [] [] = return bind
tsMatch' vts fits bind cbvs pvbs (tC:tsC) (tP:tsP)
 = do bind1 <- termMatch vts fits bind cbvs pvbs tC tP
      tsMatch vts fits bind1 cbvs pvbs tsC tsP
-- should not occur!
tsMatch' _ _ _ _ _ _ _  =  error "tsMatch': unexpected mismatch case."
\end{code}


\newpage
\section{Term-Variable Matching}

Here we are matching a candidate term \m{t_C} against a variable pattern \m{v_P}.
$$
\inferrule
   {  conditions }
   { \Gamma 
     \vdash t_C :: v_P
    \leadsto
    \beta \uplus \{ v_P \mapsto t_C \}
  }  
$$

\begin{code}
tvMatch :: MonadFail m
       => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
       -> Candidate -> Type -> Variable -> m Binding
\end{code}

First, if the candidate is a variable
we do variable-on-variable matching:
\begin{code}
tvMatch vts fits bind cbvs pbvs (Var ttC vC) ttP vP
  = vMatch vts fits bind cbvs pbvs ttC vC ttP vP
\end{code}



Otherwise we check if the pattern is
bound, known, or arbitrary,
and act accordingly.
\begin{code}
tvMatch vts fits bind cbvs pvbs tC ttP vP@(Vbl _ _ vt)
 | vt == Textual  =  fail "tvMatch: var-variable cannot match term."
 | StdVar vP `S.member` pvbs
     =  fail $ unlines
          [ "tvMatch: bound pattern cannot match term."
          , "pvbs = " ++ show pvbs
          , "vP   = " ++ show vP
          ]
 | vPmr /= UnknownVar  =  tkvMatch vts fits bind tC vPmr ttP vP
\end{code}
\subsection{Arbitrary Pattern Variable}
$$
\inferrule
   { v_P \notin B_P \cup \mathbf{dom}\,\kappa s}
   { \kappa s;\beta;B_P \vdash t_C :: v_P
    \leadsto
    \beta \uplus \{ v_P \mapsto t_C \}
  }
   \quad
   \texttt{tvMatch Arbitrary}
$$
\begin{code}
--tvMatch vts fits bind cbvs pvbs tC ttP vP@(Vbl _ vw _)
 | otherwise                  =  bindVarToTerm vP tC bind
 where
   vPmr = lookupVarTables vts vP
\end{code}

\newpage
\subsection{Known Pattern Variable}

Here the candidate term is NOT a variable term.
\begin{code}
tkvMatch :: MonadFail m => [VarTable] -> TypCmp -> Binding
       ->  Candidate -> VarMatchRole -> Type -> Variable -> m Binding
-- know vP is not in pbvs, but is in vts, known as whatP
\end{code}
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C = V~v_C
     \and
     v_P = v_C
  }
   {\kappa s;\beta;B_P \vdash t_C :: v_P
   \leadsto
   \beta \uplus \{ v_P \mapsto v_P \}}
   \quad
   \texttt{tvMatch Known-Var-Refl}
$$
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C = V~v_C
     \and
     t_C = \kappa s(v_P)
  }
   {\kappa s;\beta;B_P \vdash t_C :: v_P
    \leadsto
    \beta \uplus \{ v_P \mapsto v_C \}}
   \quad
   \texttt{tvMatch Known-Var-Var}
$$
\begin{code}
-- know vP is not in pbvs, but is in vts, known as whatP
-- THIS NEVER ARISES AS THIS FN IS ONLY USED BY tvMatch
--tkvMatch vts fits bind tC@(Var _ vC) whatP ttP vP
-- | vC == vP                                    =  bindVarToVar vP vP bind
-- | isKnownConst whatP && tC == vmrConst whatP  =  bindVarToVar vP vC bind
\end{code}
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C \neq V~v_c
     \and
     t_C = \kappa s(v_P)
  }
   {\kappa s;\beta;B_P \vdash t_C :: v_P
    \leadsto
    \beta \uplus \{ v_P \mapsto t_C \}}
   \quad
   \texttt{tvMatch Known-Var-TVal}
$$
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C : T
     \and
     \kappa s(v_P) : T
  }
   {\kappa s;\beta;B_P \vdash t_C :: v_P
    \leadsto
    \beta \uplus \{ v_P \mapsto t_C \}}
   \quad
   \texttt{tvMatch Known-Var-TType}
$$
\begin{code}
-- know vP is not in pbvs, but is in vts, known as whatP
tkvMatch vts fits bind tC whatP ttP vP
 | isKnownVar whatP = fail "tkvMatch: known-var can only match self"
 | isKnownConst whatP && tC == vmrConst whatP  =  bindVarToTerm vP tC bind
 | isEType ttP && isKnownVar whatP
   && vmrType whatP == ttP                     =  bindVarToTerm vP tC bind
tkvMatch _ _ _ _ _ _ _ = fail "tkvMatch: candidate not this known variable."
\end{code}

\newpage
\section{Variable Matching}

Now, onto variable matching:
\begin{code}
vMatch :: MonadFail m
       => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
       -> Type -> Variable -> Type -> Variable
       -> m Binding
\end{code}
The rules regarding suitable matches for pattern variables
depend on: 
what class of variable we have,
the temporalities,
and what we know about them (\texttt{VarMatchRole}).
We screen them in that order.
We do not have type information here, 
but that is screened before we get here.

What bindings make sense from a class and type perspective? 
Consider observation variables $x$ and $y$, 
expression variables $e$ and $f$, 
and predicate variables $P$ and $Q$.

\begin{tabular}{|c|l|}
\hline
Match Binding & Commentary
\\\hline\hline
 $x \mapsto  y$ & OK
\\\hline
 $x \mapsto f$ or $x \mapsto Q$
 & doesn't work (think free-variables)
\\\hline
 $e \mapsto  f$ & OK
\\\hline
 $e \mapsto  y$ & OK, $y$ is a simple expr.
\\\hline
 $e \mapsto  Q$ & OK
\\\hline
 $P \mapsto  Q$ & OK
\\\hline
 $P \mapsto x$ & Here $x$ should be $\Bool$.
\\\hline
 $P \mapsto f$ & Here $f$ should be $t^n \fun\Bool, ~~n \geq 0$.
\\\hline
\end{tabular}

Rules based on the static or dynamic nature of variables:
\begin{itemize}
  \item Static variables can match static or dynamic variables.
  \item Dynamic variables can only match those that have the
  same \texttt{VarWhen} value,
  except that the string in \texttt{During} may differ.
\end{itemize}
We first screen by variable class:
\begin{code}
vMatch vts fits bind cbvs pvbs ttC vC@(Vbl _ vwC _) ttP vP@(Vbl _ vwP _)
  | vwC == vwP   =  vMatch' vts fits bind cbvs pvbs vC vP
  | vwP /= ObsV  =  vMatch' vts fits bind cbvs pvbs vC vP
  | otherwise    =  fail $ unlines [ "vMatch: class mismatch"
                                 , "vC = " ++ show vC
                                 , "vP = " ++ show vP ]
\end{code}
Here variable class are compatible, 
so we now screen based on temporality:
\begin{code}
vMatch' vts fits bind cbvs pvbs vC vP
  | whenVarMatches vC vP  =  vMatch'' vts fits bind cbvs pvbs vC vP
  | otherwise             =  fail $ unlines [ "vMatch: temporality mismatch"
                                            , "vC = " ++ show vC
                                            , "vP = " ++ show vP ]
\end{code}

We then check for bound-variables
\begin{code}
vMatch'' vts fits bind cbvs pvbs vC vP
  | pbound     =  bvMatch   vts fits bind cbvs vC vP
  | otherwise  =  vMatch''' vts fits bind vmr  vC vP
  where
    pbound = StdVar vP `S.member` pvbs
    vmr = lookupVarTables vts vP
\end{code}
Next, rules based on knowledge about the pattern variable:

\begin{tabular}{|c|c|c|}
\hline
Knowledge & \texttt{VarMatchRole} & Allowed Candidates
\\\hline\hline
Unknown & \texttt{UnknownVar} & Anything as per classification.
\\\hline
Known variable & \texttt{KnownVar} & Itself only
\\\hline
Known constant & \texttt{KnownTerm} & Itself or the constant
\\\hline
Generic variable & \texttt{GenericVar}
 & Itself or any \texttt{InstanceVar} that references this.
\\\hline
Instance variable & \texttt{InstanceVar} & Itself only
\\\hline
\end{tabular}
\begin{code}
vMatch''' _ _ bind UnknownVar   vC vP  =  bindVarToVar vP vC bind
vMatch''' _ _ bind (KnownVar _ _) vC vP
  | vC == vP                           =  bindVarToVar vP vC bind
vMatch''' _ _ bind (KnownTerm (Var _ v)) vC vP
  | vC == v                            =  bindVarToVar vP vC bind
vMatch''' vts fits bind GenericVar vC vP
  = case lookupVarTables vts vC of
      (InstanceVar v) | v == vP     ->  bindVarToVar vP vC bind
      _ ->  fail $ unlines [ "vMatch: wrong generic"
                           , "vC = " ++ show vC
                           , "vP = " ++ show vP ]
vMatch''' _ _ _ what vC vP  =  fail $ unlines [ "vMatch: knowledge mismatch."
                                            , "vC = " ++ show vC
                                            , "vP = " ++ show vP
                                            , "what(vP) = " ++ show what
                                            ]
\end{code}

\subsection{Bound Pattern Variable}
$$
\inferrule
   { v_P \in B_P
      \and
     v_C \in B_C
   }
   {\beta;(B_C,B_P) \vdash v_C :: v_P
    \leadsto \beta \uplus \{ v_P \mapsto v_C \}}
   \quad
   \texttt{vMatch Bound-Var}
$$
In addition, both variables must have the same class.
\begin{code}
bvMatch :: MonadFail m => [VarTable] -> TypCmp -> Binding -> CBVS
        -> Variable -> Variable -> m Binding
-- we know vP is in pbvs
bvMatch vts fits bind cbvs vC@(Vbl _ vwC _) vP@(Vbl _ vwP _)
 | vwC /= vwP  =  fail "bvMatch: variable class mismatch."
 | StdVar vC `S.member` cbvs  =  bindVarToVar vP vC bind
 | otherwise  =  fail "bvMatch: candidate not a bound variable."
\end{code}

\newpage
\section{Collection Matching}
\label{ssec:coll-matching}

There are a number of ``collections'' we have to match,
including variable lists and sets, and substitutions.
There collections always have two sub-parts:
one sub-part consists of ``single/standard/ordinary'' elements,
while the other sub-parts have ``set/list/collection'' elements that stand for collections
(possibly empty) of both kinds of elements.

As patterns,
each single element must match exactly one candidate single element,
while each collection element can match a collection
of both single and collection candidate elements.

We will write a pattern collection in the form
$$
  ( (a_1, \dots, a_m), (\lst b_1, \dots, \lst b_n) )
$$
where $a_i$ are single pattern elements,
and $\lst b_j$ are collection pattern elements.

Let us denote a candidate collection as:
$$
 ( (c_1, \dots, c_p ), ( \lst d_1, \dots, \lst d_q ) )
$$
For a match to be possible at all, the following constraints
must be satisfied:
\begin{eqnarray*}
   && p \geq m
\\ p > m &\implies& n > 0
\\ n = 0 &\implies& p = m \land q = 0
\\ q > 0 &\implies& n > 0
\end{eqnarray*}
We can code this up as follows%
\footnote{Optional exercise!}%
:
\begin{code}
isFeasibleCollMatch(m,n,p,q)
 | p < m      =  False
 | n > 0      =  True
 | otherwise  =  p == m && q == 0
\end{code}

\textbf{Note: }\textsl{
We really should have a series of matching combinators,
because the same matching issues keep arising.
We have to match list-based and set-based collections
as well as those where the elements are pairs,
as found in substitutions.
We should also have combinators for partial matches that arise
when doing initial matching of the single collection parts,
where some candidates may be leftover, to be bound by collection variables.
}

\newpage
\section{Variable-List Matching}

\begin{code}
vlMatch :: (MonadPlus mp, MonadFail mp) => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
        -> VarList -> VarList -> mp Binding
\end{code}


Matching a non-empty candidate variable-list
against a non-empty pattern variable-list is non-trivial,
so we perform a number of phases.
The first phase tries to reconcile the pre-existing bindings
with the pattern variables.
If this succeeds,
we will have removed the already bound portions
from both variable lists,
resulting in a smaller ``freer'' problem.
This can then be solved in turn.

This kind of match will always fail
if any of the candidate or pattern list-variables are recorded as
\texttt{KnownVarSet}, or already in the bindings so far as \texttt{BindSet}.

\begin{code}
-- we expect both vlC and vlP to be non-null here, at top level
-- this is because binders don't have null binder containers.
vlMatch vts fits bind cbvs pbvs vlC [] = fail "vlMatch: null pattern."
vlMatch vts fits bind cbvs pbvs [] vlP = fail "vlMatch: null candidate."
vlMatch vts fits bind cbvs pbvs vlC vlP
  = do (vlC',vlP') <- applyBindingsToLists bind vlC vlP
       vlFreeMatch vts fits bind cbvs pbvs vlC' vlP'
\end{code}

\subsection{Applying Bindings to Lists}

We simply walk up the pattern looking for variables
already bound, and then search for what they are bound to, in the candidate
list.
We remove both, and continue.

We use tail-recursion and accumulate the un-bound (or ``free'') part of both
lists.
\begin{code}
applyBindingsToLists :: (MonadPlus mp, MonadFail mp)
                 => Binding -> VarList -> VarList -> mp (VarList,VarList)
applyBindingsToLists bind vlC vlP
  = applyBindingsToLists' bind [] [] vlC vlP

applyBindingsToLists' :: (MonadPlus mp, MonadFail mp)
                 => Binding
                 -> VarList -> VarList
                 -> VarList -> VarList -> mp (VarList,VarList)
\end{code}

Pattern list null: we are done, return the leftovers
\begin{code}
applyBindingsToLists' bind vlC' vlP' vlC []
  = return ((reverse vlC')++vlC, reverse vlP')
\end{code}

First pattern variable is standard:
\begin{code}
applyBindingsToLists' bind vlC' vlP' vlC (gP@(StdVar vP):vlP)
 = case lookupVarBind bind vP of
    Nothing           -> applyBindingsToLists' bind vlC' (gP:vlP') vlC vlP
    Just (BindTerm _) -> fail "vlMatch: pattern var already bound to term"
    Just (BindVar vB) -> findStdCandidate bind vlC' vlP' vlC vB vlP
\end{code}

First pattern variable is a list-variable:
\begin{code}
applyBindingsToLists' bind vlC' vlP' vlC (gP@(LstVar lvP):vlP)
 = case lookupLstBind bind lvP of
    Nothing  -> applyBindingsToLists' bind vlC' (gP:vlP') vlC vlP
    Just (BindList vlB) -> findLstCandidate bind vlC' vlP' vlC vlB vlP
    _ -> fail "vlMatch: list-variable bound to variable-set."
\end{code}

\newpage
\subsubsection{Find Standard Pattern-Variable Binding}
Found \texttt{vP} bound to \texttt{vB}.
Now need to search \texttt{vlC} for \texttt{vB}.
\begin{code}
findStdCandidate bind vlC' vlP' [] vB vlP
  = fail $ unlines
      [ "vlMatch: std-pattern var's binding not in candidate list"
      , "bind = " ++ show bind
      , "vlC' = " ++ show vlC'
      , "vlP' = " ++ show vlP'
      , "vB = " ++ show vB
      , "vlP = " ++ show vlP
      ]
findStdCandidate bind vlC' vlP' (gC@(StdVar vC):vlC) vB vlP
 | vC == vB  = applyBindingsToLists' bind vlC' vlP' vlC vlP
 | otherwise = findStdCandidate bind (gC:vlC') vlP' vlC vB vlP
findStdCandidate bind vlC' vlP' (gC:vlC) vB vlP
  =  findStdCandidate bind (gC:vlC') vlP' vlC vB vlP
\end{code}

\subsubsection{Find List Pattern-Variable Binding}
Found \texttt{vlP} bound to \texttt{vlB}.
Now need to search \texttt{vlC} for \texttt{vlB}.
\begin{code}
findLstCandidate bind vlC' vlP' vlC [] vlP
  = applyBindingsToLists' bind vlC' vlP' vlC vlP
findLstCandidate bind vlC' vlP' [] vlB vlP
  = fail "vlMatch: pattern list-var's binding not in candidate list"
findLstCandidate bind vlC' vlP' vlC@(gC:vlC_) vlB@(gB:vlB_) vlP
 | gC == gB && found
   = applyBindingsToLists' bind vlC' vlP' vlCrest vlP
 | otherwise = findLstCandidate bind (gC:vlC') vlP' vlC_ vlB vlP
 where
  (found,vlCrest) = vlB_ `pulledFrom` vlC_
\end{code}

\newpage
\subsection{Free Variable-List Matching}

Here we are doing variable-list matching where all of the
pattern variables are unbound.
We do not attempt a complete solution,
as in fact there can be many possible bindings.
We adopt a heuristic that simply walks the pattern list
from left to right and tries to bind the head pattern variable
against some prefix of the candidate list.
\begin{code}
vlFreeMatch :: (MonadPlus mp, MonadFail mp)
              => [VarTable] -> TypCmp -> Binding
              -> CBVS -> PBVS
              -> VarList -> VarList
              -> mp Binding
\end{code}

If both lists are empty, we are done:
\begin{code}
vlFreeMatch vts fits bind cbvs pbvs [] [] = return bind
\end{code}

If there are leftover candidate variables, we fail
\begin{code}
vlFreeMatch vts fits bind cbvs pbvs vlC []
  = fail "vlMatch: too many candidate variables."
\end{code}

Standard pattern variable matches are easy.
The head of the candidate list must be a pattern variable.
It must also match according to the rules for variable matching.
\begin{code}
vlFreeMatch vts fits bind cbvs pbvs [] (StdVar vP:_)
  = fail "vlMatch: too many std. pattern variables."

vlFreeMatch vts fits bind cbvs pbvs ((StdVar vC):vlC) ((StdVar vP):vlP)
  = do bind' <- vMatch vts fits bind cbvs pbvs ArbType vC ArbType vP
       vlFreeMatch vts fits bind' cbvs pbvs vlC vlP

vlFreeMatch vts fits bind cbvs pbvs vlC ((StdVar _):_)
  = fail "vlMatch: std pattern cannot match list candidate."
\end{code}

\newpage
A pattern list-variable can match zero or more candidate general variables.
If it is known, it can only match itself,
or, if not abstract, against the list against which it is defined.
If unknown, we come face-to-face with non-determinism.
For now we simply attempt to match by letting the list-variable
match the next $n$ candidate variables, for $n$ in the range $0\dots N$,
for some fixed $N$.
For now, we take $N=2$.
\begin{code}
vlFreeMatch vts fits bind cbvs pbvs vlC (gvP@(LstVar lvP):vlP)
  = let bc = lvarClass lvP in
    case expandKnown vts lvP of
     Nothing
       -> vlFreeMatchN vts fits bind cbvs pbvs bc vlC lvP vlP 0
          `mplus`
          vlFreeMatchN vts fits bind cbvs pbvs bc vlC lvP vlP 1
          `mplus`
          vlFreeMatchN vts fits bind cbvs pbvs bc vlC lvP vlP 2
     Just (AbstractList, uis, ujs)
       | null vlC -> fail "vlMatch: not enough candidates."
       | gvP /= head vlC  ->  fail "vlMatch: abstract lvar. only matches self."
       | otherwise
           -> do bind' <- bindLVarToVList lvP [gvP] bind
                 vlFreeMatch vts fits bind' cbvs pbvs (tail vlC) vlP
     Just kX@(KnownVarList vlK vlX xLen, uis, ujs)
       | length uis > length vlX
          -> fail "vlMatch: invalid known epxansion"
       | otherwise
          -> do (bind',vlC') <- vlKnownMatch vts fits bind cbvs pbvs
                                     bc vlC gvP vlK vlX uis ujs
                vlFreeMatch vts fits bind' cbvs pbvs vlC' vlP
     _ -> fail "vlMatch: pattern list-variable is set-valued."
\end{code}

We have a simple, ``slightly greedy'' algorithm
that matches a list-variable against the first \texttt{n} candidates.
\begin{code}
vlFreeMatchN vts fits bind cbvs pbvs bc vlC lvP vlP n
  | precise
     =  do bind' <- bindLVarToVList lvP firstnC bind
           vlFreeMatch vts fits bind' cbvs pbvs restC vlP
  | otherwise  =  fail "vlFreeMatchN: vlC too short."
 where
    (firstnC,restC)  =  splitAt n vlC
    precise = length firstnC == n
\end{code}
\textbf{Note: }\textsl{
The code here used to match all of the candidate-list if its length was not greater
that parameter $n$.
So candidate list of length 1 would succeed for $n\geq 1$,
thus explaining why we used to get the same match several times.
}

\newpage
\subsubsection{Matching a List-Variable, known to be a list.}
First we handle simple cases, where either the list-variable,
its definition, or its expansion as variables,
are a prefix of the candidate list.
\begin{code}
-- not null vlC
vlKnownMatch vts fits bind cbvs pbvs
                bc vlC gvP vlK vlX uis ujs
 | not (null vlC) && gvP == head vlC -- covers lvP known to be Abstract
    = do bind' <- bindLVarToVList lvP [gvP] bind
         return (bind',tail vlC)
 | vlK `isPrefixOf` vlC && null uis
    = do bind' <- bindLVarToVList lvP vlK bind
         bind'' <- bindLVarsToNull bind' (map (lvr bc vw) ujs)
         return (bind'',vlC \\ vlK)
 | gvlX `isPrefixOf` vlC && null uis
    = do bind' <- bindLVarToVList lvP gvlX bind
         bind'' <- bindLVarsToNull bind' (map (lvr bc vw) ujs)
         return (bind'',vlC \\ gvlX)
 | otherwise -- now for the hard stuff !!
    = do (bind',vlC1,vlC2)
           <- vlExpandMatch
                (vts,bc,vw)   -- static context
                (bind,[],[])  -- dynamic context
                vlC
                (vlX,uis,ujs,length vlX-length uis) -- pattern expansion
         bind'' <- bindLVarToVList lvP vlC1 bind'
         return (bind'',vlC2)
 where
    (LstVar lvP) = gvP
    gvlX = map StdVar vlX
    vw = lvarWhen lvP
    lvr vc vw i = LVbl (Vbl i vc vw) [] []
\end{code}

\newpage
\subsection{Known List-Var Expansion Matching (List)}

\subsubsection{Classifying Expansions}
Consider an expansion
$( x_1,\dots,x_m
   \setminus
   v_1,\dots,v_n
   ;
   l_1,\dots,l_k )
$
where the $x_i$ and $v_j$ are disjoint.

If $n > m$, we consider it ill-formed.
If $n = m$, then it denotes an empty list,
and the $l_i$, if any, denote empty lists of variables
This leads to a first classification:

\begin{tabular}{|l|c|}
\hline
  empty & $ m = n $
\\\hline
 non-empty & $ m > n $
\\\hline
\end{tabular}

If $k = 0$, then it denotes a list of length $m-n$,
that is interleaved within the $\seqof{x_1,\dots,x_m}$ list.
If $k = 0$ and $n = 0$,
then it denotes precisely the list $\seqof{x_1,\dots,x_m}$.
This leads to a second classification (orthogonal to the first):

\begin{tabular}{|l|c|}
\hline
  inexact & $k > 0$
\\\hline
  exact &  $k = 0, n > 0$
\\\hline
  rigid & $k=0, n=0$
\\\hline
\end{tabular}

A key metric is the range of possible lengths that an expansion can have:
\begin{eqnarray*}
  range(\seqof{v_1,\dots,v_n} \setminus \mathtt{uv} ; \mathtt{ul})
  &=& \left\{
        \begin{array}{lr}
          ~(n-len(\mathtt{uv})), & \mathtt{ul} = \nil
         \\
          ~[0\dots(n-len(\mathtt{uv}))], & \mathtt{ul} \neq \nil
        \end{array}
      \right.
\end{eqnarray*}


\subsubsection{Matching the list-expansion of a List-Variable.}
We now try to match (all of) \texttt{lvP} incrementally
against a prefix of \texttt{vlC},
using the full expansion, \texttt{vlX} and candidate variables
as we go along.
\begin{eqnarray*}
   expand(\mathtt{lvP})
   &=&
   \seqof{vp_1,\dots,vp_m} \setminus \mathtt{uvP} ; \mathtt{ulP}
\\ \mathtt{vlC}
   &=&
   \seqof{gc_1,\dots,gc_k,gc_{k+1},\dots,gc_n}
\end{eqnarray*}
If this succeeds, we return a binding between the original \texttt{lvP}
and the corresponding prefix of the original \texttt{vlC},
as well as the remaining suffix of \texttt{vlC}.
\begin{eqnarray*}
   \mathtt{vlC} :: \mathtt{lvP}
   &\leadsto&
   (\mathtt{lvP}\mapsto\seqof{gc_1,\dots,gc_k}
   ,\seqof{gc_{k+1},\dots,gc_n})
\end{eqnarray*}

We now present a formal description of the algorithm,
by introducing a context that includes bindings, among other things.
We are trying to perform the following partial-match ($\mvl$) inference:
\begin{eqnarray*}
  \dots,\beta
  \vdash
  \seqof{gc_1,\dots,gc_k,gc_{k+1},\dots,gc_n} \mvl \mathtt{vlP}
  \leadsto
  (\beta'\override\maplet{\mathtt{vlP}}{\seqof{gc_1,\dots,gc_k}},\seqof{gc_{k+1},\dots,gc_n})
\end{eqnarray*}
Here $\dots$ denotes further context to be elucidated,
while $\beta'$ indicates that there may be other bindings,
in particular associated with subtracted variables in \texttt{vlP}.
We use $\Gamma$ below to denote the complete context,
and $\gamma,x,y$ to denote context components $x$ and $y$
collected together with $\gamma$, the rest of the context.

We can break the algorithm down into a number of levels
of matching rules:

\begin{tabular}{|c|l|}
\hline
 Symbol & Description
\\\hline
 $\mvl$ & all of pattern list-variable against prefix of candidate list
\\\hline
 $\mvlx$ & all of pattern expansion against prefix of candidate list
\\\hline
 $\mvlxx$ & prefix of pattern expansion against all of candidate expansion
\\\hline
\end{tabular}

\textbf{An issue we need to consider is how these rules work
if \texttt{vlC} is an empty list to begin with,
or contains one or two `empty' known list variables.}
%\adobesucks

\newpage

\subsubsection{Rules for $\mvl$ ---}~

We first start by expanding \texttt{vlP}  as \texttt{xP}
(or \texttt{(xsP,uvP,ulP)}) and using the expansion as the basis
for mapping.
This is what done by \texttt{vlKnownMatch} above
when it calls \texttt{vlExpandMatch} (a.k.a. $\mvlx$) below.
We have a dynamic context $\Gamma=(\beta,\kappa,\ell)$
that evolves as matching progresses,
as well as a static context used for known list-var.
expansion ($expand$), that is not shown below.
The binding passed in, modified and returned
by matching is denoted by $\beta$.
We use $\kappa$
to track the candidate variables matches so far,
and $\ell$  records pattern expansion variables
that will correspond to subtracted pattern list-variables.
\[
\knownLMatchR
\]
%%

\subsubsection{Rules for $\mvlx$ ---}~

\begin{enumerate}
%%%%
\item
The plan with $\mvlx$ is to map successive `prefixes' of the \texttt{vlP} expansion
against the expansion of variables, one-by-one in \texttt{vlC}, until
we reduce $\mathtt{xP}$ to `empty'.
The simplest case is when \texttt{vlP} is empty:
\[
\expandLMatchEmptyR
\]
An open question here is what we do with any remaining subtracted
variables in the pattern. They may need to be bound appropriately.
This is the purpose of the $blo$ (bind-leftovers) function.
The $blo$ function satisfies the following specification:
\bloLDef
%%
\item
 When \texttt{vlC} is empty and \texttt{vlP} is inexact,
 we terminate, binding leftovers.
\[
\expandLMatchInExactR
\]
\item
If \texttt{xP} is not empty,
then we match a prefix of it against all of the expansion of the first
variable in \texttt{vlC}.
If that succeeds then we add the variable to $\kappa$, and recurse.
\[
\expandLMatchNonEmptyR
\]
%%
%%%%
\end{enumerate}



\subsubsection{Rules for $\mvlxx$ ---}~

\begin{enumerate}
%%%%
\item
  We are now using $\mvlxx$ to compare a candidate expansion with a pattern expansion,
  trying to match all of the candidate with a prefix of the expansion.
  \[
   \Gamma
      \vdash
      \mathtt{xC} \mvlxx \mathtt{xP}
      \leadsto ( \beta',\ell',\mathtt{xP'} )
  \]
  If both are empty, we are done:
\[
\expTwoLMatchAllEmptyR
\]
If the pattern is empty, but the candidate is not, then we fail.
If the candidate is empty, but the pattern is not,
then we return:
\[
\expTwoLMatchCandEmptyR
\]
%%
\item
If both expansions are non-empty, then we compare the first two variables
in their expansions.
If they are the same, remove both and recurse:
\[
\expTwoLMatchSameR
\]
%%
\item
If they differ,then we need to consider the size-ranges
of both sides to consider what action to take.
If both sides are rigid then the match fails.
The pattern size range must never be smaller than that for the candidate,
for a match to succeed.
In either case, a variable can only be removed from either side
by offsetting against a subtracted unknown variable from the
corresponding side, which is therefore itself also removed.
This action of removing a leading expansion variable,
and an offsetting subtracted variable is called `shrinking'.`
Any such removal on the pattern side must bind that subtracted variable
to the removed expansion variable, noting that the subtracted variable
may have already been bound in a wider matching context.
\par
In effect we determine conditions for which it is valid
to remove either a candidate or pattern variable.
If both can be removed, then we allow a non-deterministic choice
between which one we do.
%%
\item
We can always shrink an non-rigid non-empty candidate expansion
when \texttt{uvC} is non-null:
\[
\expTwoLMatchClipCandR
\]
%%
\item
We can always shrink an non-rigid non-empty pattern expansion
when \texttt{uvP} is non-null:
\[
\expTwoLMatchClipPatnR
\]
%%
\item
When \texttt{xC} is inexact, and \texttt{uvC} is nil
we can simply remove the leading candidate expansion variable,
but leave \texttt{ulC} untouched.
We do not care which members of \texttt{ulC} cover which members
of the candidate expansion list.
\[
\expTwoLMatchSqueezeCR
\]
Reminder: we can never shrink the candidate if it is rigid.
%%
\item
When \texttt{xP} is inexact, and \texttt{uvP} is nil,
and the pattern size is greater than that of the candidate,
then we can remove the leading pattern expansion variable.
However we must record its removal, so that at the end,
we can decide how to map the members of \texttt{ulP}
to all pattern variables removed in this way.
The record of all such variables is held in the $\ell$
components of the context.
\[
\expTwoLMatchSqueezePR
\]

Reminder: we can never shrink the pattern if it is rigid.
%%%%
\end{enumerate}

\newpage

First, expansion lists and predicates over them.
\begin{code}
type LExpansion
 = ( [Variable]    --  xs, full expansion less known subtractions
   , [Identifier]  --  uv, subtracted variable identifiers
   , [Identifier]  --  ul, subtracted list-variable identifiers
   , Int           --  size = length xs - length uv
   )

emptyE (_,_,_,s) = s == 0
inexactE (_,_,[],_) = False
inexactE _ = True
exactE (_,(_:_),[],_) = True
exactE _ = False
rigidE (_,[],[],_) = True
rigidE _ = False
\end{code}

\newpage
\bloLDef
We need part of the static context here.
\begin{code}
-- blo to be defined here
bindLeftOvers :: (MonadPlus mp, MonadFail mp)
              => ( [VarTable], VarClass, VarWhen ) -- static context
              -> Binding
              -> [Variable]   -- expansion variables ( ell ++ xs)
              -> [Identifier] -- subtracted variables
              -> [Identifier] -- subtracted list-variables
              -> mp Binding
bindLeftOvers (vts,bc,bw) bind xs us ls
  = do (bind',xs') <- bloVars bind xs us
       bloLVars bind' xs' ls
  where

    bloVars bind xs []  =  return (bind,xs)
    bloVars bind []  _  =  fail "bindLeftOvers: too few expansion vars."
    bloVars bind xs (ui:us)
      = case lookupVarBind bind uv of
          Nothing
            ->  do bind' <- bindVarToVar uv (head xs) bind
                   bloVars bind' (tail xs) us
          Just (BindVar v)
            ->  do xs' <- getitem v xs
                   bloVars bind xs' us
          _ ->  fail "bindLeftOvers: subtract bound to term"
      where
        uv = Vbl ui bc bw

    bloLVars bind [] [] = return bind
    bloLVars bind xs [ui]
      = bindLVarToVList lv (map StdVar xs) bind
      where lv = LVbl (Vbl ui bc bw) [] []
    bloLVars bind xs (ui:ul)
      = case lookupLstBind bind lv of
         Nothing
           -> do bind' <- bindLVarToVList lv [] bind
                 bloLVars bind' xs ul
         Just (BindList vs)
           ->  do xs' <- getvars xs vs
                  bloLVars bind xs' ul
         _ -> fail "bindLeftOvers: subtract not bound to list"
      where
        lv = LVbl (Vbl ui bc bw) [] []

    getvars xs [] = return xs
    getvars xs (StdVar v:rest)
     = do xs' <- getitem v xs
          getvars xs rest
    getvars _ _ = fail "bindLeftOvers: subtract bound contains list-vars"
\end{code}

\newpage
\begin{code}
vlExpandMatch :: (MonadPlus mp, MonadFail mp)
              => ( [VarTable], VarClass, VarWhen ) -- static context
              -> ( Binding, VarList, [Variable] )  -- dynamic context
              -> VarList -- candidate variable list.
              -> LExpansion  -- pattern list-variable expansion
              -> mp ( Binding  -- resulting binding
                    , VarList  -- matched candidate prefix
                    , VarList  -- remaining candidate suffix
                    )
\end{code}


\[
\expandLMatchEmptyR
\]
\[
\expandLMatchInExactR
\]
\[
\expandLMatchNonEmptyR
\]

\begin{code}
vlExpandMatch sctxt@(vts,bc,bw) dctxt@(bind,kappa,ell) vlC xP@(xs,uv,ul,_)
  | emptyE xP || (inexactE xP && null vlC)
     = do bind' <-  bindLeftOvers sctxt bind (reverse ell++xs) uv ul
          return (bind',reverse kappa,vlC)
  | not $ null vlC
     =  let (vC:vlC') = vlC in
        do xC <- expand vC
           (bind',ell',xP') <- vlExpand2Match sctxt dctxt xC xP
           vlExpandMatch sctxt (bind,vC:kappa,ell') vlC' xP'
  | otherwise = fail "vlExpandMatch: null candidate for exact, non-empty pattern."

  where
    expand (StdVar v)  = return ([v],[],[],1)
    expand (LstVar lv)
      = case expandKnown vts lv of
          Just (KnownVarList vlK vlX _,uis, ujs)
            -> return (vlX,uis,ujs,length vlX - length uis)
          _ ->  fail "vlExpandMatch: candidate is unknown list-var."
\end{code}

\newpage
\begin{code}
vlExpand2Match :: (MonadPlus mp, MonadFail mp)
               => ( [VarTable], VarClass, VarWhen ) -- static context
               -> ( Binding, VarList, [Variable] )  -- dynamic context
              -> LExpansion  -- candidate variable expansion
              -> LExpansion  -- pattern list-variable expansion
              -> mp ( Binding  -- resulting binding
                    , [Variable]  -- subtracted parts of candidate expansion
                    , LExpansion   -- remaining pattern expansion
                    )
\end{code}

\[
\expTwoLMatchAllEmptyR
\qquad
\expTwoLMatchCandEmptyR
\]

\begin{code}
vlExpand2Match _ dctxt@(bind,_,ell) xC xP
 | emptyE xC  =  return (bind,ell,xP)
\end{code}

\[
\expTwoLMatchSameR
\]
\begin{code}
vlExpand2Match sctxt dctxt xC@(vC:xsC,uvC,ulC,szC) xP@(vP:xsP,uvP,ulP,szP)
  | vC == vP  =  vlExpand2Match sctxt dctxt (xsC,uvC,ulC,szC-1)
                                            (xsP,uvP,ulP,szP-1)
  | otherwise
      =  vlShrinkCandMatch sctxt dctxt xC xP
         `mplus`
         vlShrinkPatnMatch sctxt dctxt xC xP
\end{code}
\textbf{Note: }\textsl{
Could this code cause ``doubled-up'' matches?
}

\[
\expTwoLMatchSqueezeCR
\]
\[
\expTwoLMatchClipCandR
\]

\begin{code}
vlShrinkCandMatch sctxt dctxt xC@(vC:xsC,uvC,ulC,szC) xP
  | null uvC && null ulC
    = fail "vlShrinkCandMatch: cannot shrink rigid candidate expansion"
  | null uvC -- && not (null ulC)
     = vlExpand2Match sctxt dctxt (xsC,uvC,ulC,szC-1) xP
  | otherwise -- not (null uvC)
     = vlExpand2Match sctxt dctxt (xsC,tail uvC,ulC,szC) xP
\end{code}

\newpage
\[
\expTwoLMatchSqueezePR
\]
\[
\expTwoLMatchClipPatnR
\]
\begin{code}
vlShrinkPatnMatch sctxt@(_,bc,bw) (bind,gamma,ell)
                  xC@(_,_,_,szC) xP@(vP:xsP,uvP,ulP,szP)
  | null uvP && null ulP
    = fail "vlShrinkPatnMatch: cannot shrink rigid pattern expansion"
  | null uvP && szP > szC -- && not null (ulP)
    = vlExpand2Match sctxt (bind,gamma,vP:ell) xC (xsP,uvP,ulP,szP-1)
  | not (null uvP)
     = do vu <- select bind vP Nothing uvP
          bind' <- bindVarToVar vu vP bind
          vlExpand2Match sctxt (bind',gamma,vP:ell) xC (xsP,uvP,ulP,szP)
  | otherwise = fail "vlShrinkPatnMatch: match fail."
  where

    select bind vP Nothing []  = fail "vlShrinkPatnMatch: no suitable vu found."
    select bind vP (Just vu) []  = return vu
    select bind vP mvu (ui:uvP)
     = let vu = Vbl ui bc bw in
         case lookupVarBind bind vu of
           Nothing -> select bind vP (upd mvu vu) uvP
           Just (BindVar x)
             | x == vP    ->  return vu
             | otherwise  ->  select bind vP mvu uvP
           _ -> fail "vlShrinkPatnMatch: subtracted var bound to term."

    upd Nothing x = Just x
    upd mx      _ = mx
\end{code}

\newpage
\section{Variable-Set Matching}

We follow a similar pattern to variable-list matching.
First apply any bindings we have, and then try to match what is left.
The key difference here, obviously, is that order does not matter.
\begin{code}
vsMatch :: (MonadPlus mp, MonadFail mp) => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
        -> VarSet -> VarSet -> mp Binding
vsMatch vts fits bind cbvs pbvc vsC vsP = do
  (vsC',vsP') <- applyBindingsToSets vts bind vsC vsP
  vsFreeMatch vts fits bind cbvs pbvc vsC' vsP'
\end{code}

\subsection{Applying Bindings to Sets}

\begin{code}
applyBindingsToSets
  :: (MonadPlus mp, MonadFail mp)
  => [VarTable] -> Binding -> VarSet -> VarSet -> mp (VarSet,VarSet)
applyBindingsToSets vts bind vsC vsP
 = applyBindingsToSets' vts bind [] vsC $ S.toList vsP

applyBindingsToSets'
  :: (MonadPlus mp, MonadFail mp)
  => [VarTable] -> Binding -> VarList -> VarSet -> VarList -> mp (VarSet,VarSet)
\end{code}

Pattern list (set) empty, return the leftovers
\begin{code}
applyBindingsToSets' vts bind vlP vsC [] = return (vsC,S.fromList vlP)
\end{code}

When the first pattern variable is standard:
\begin{code}
applyBindingsToSets' vts bind vlP' vsC (gP@(StdVar vP):vlP)
 = case lookupVarBind bind vP of
    Nothing -> applyBindingsToSets' vts bind (gP:vlP') vsC vlP
    Just (BindTerm _) -> fail "vsMatch: pattern var already bound to term."
    Just (BindVar vB)
     -> let gB = StdVar vB in
        if gB `insideS` vsC
        then applyBindingsToSets' vts bind vlP' (S.delete gB vsC) vlP
        else fail "vsMatch: std-pattern var binding not in candidate set."
\end{code}

\newpage
When the first pattern variable is a list-variable:
\begin{code}
applyBindingsToSets' vts bind vlP' vsC (gP@(LstVar lvP):vlP)
 = case lookupLstBind bind lvP of
    Nothing -> applyBindingsToSets' vts bind (gP:vlP') vsC vlP
    Just (BindSet vsB) -> checkBinding vts vsB
    Just (BindList vlB) -> checkBinding vts $ S.fromList vlB
    Just (BindTLVs tlvs)
      | all isVar ts
         -> checkBinding vts
            $ S.fromList (map (StdVar . theVar) ts ++ map LstVar lvs)
      | otherwise
          -> fail "vsMatch: list-variable bound to at least one non-Var term"
      where
        ts :: [Term]
        ts = tmsOf tlvs
        lvs :: [ListVar]
        lvs = lvsOf tlvs
  where
    checkBinding vts vsB 
      | vsBS `withinS` vsCS
        = applyBindingsToSets' vts bind vlP' (vsCS `removeS` vsBS) vlP
      | vsBSx `withinS` vsCSx
        = applyBindingsToSets' vts bind vlP' (vsCSx `removeS` vsBS) vlP
      | otherwise
        = fail $ unlines'
           [ "vsMatch: pattern list-var binding not in candidate set."
           , show bind ]
       where
         vsBS = subsumeS vsB
         vsBSx = mapVToverVarSet vts vsB
         vsCS = subsumeS vsC
         vsCSx = mapVToverVarSet vts vsCS
\end{code}

\newpage
\subsection{Free Variable-Set Matching}

Here we are doing variable-set matching where all of the
pattern variables are unbound.
We do not attempt a complete solution,
as in fact there can be many possible bindings.

In each \texttt{VarSet} we have four types of entities:
\begin{description}
  \item[Unknown Variables] can match any variable;
  \item[Known Variables] can only match themselves;
  \item[Unknown List-Variables] can match any set,
   empty or otherwise, of general variables;
  \item[Known List-Variables] can only match themselves
    or a  set of variables consistent with their possible expansions,
    as moderated by their subtractions.
\end{description}
The matching strategy is to start with the known pattern variables,
and ensure all are present in the candidate.
If so, remove them from both and continue, otherwise fail.
We also deal with known pattern list-variables that can match themselves
on the fly.

\textbf{RE-THINK}
\textit{
If we require that known-container-variables induce a partition
of known-std-variables then we can induce a mapping from
known-std-variables to a sequence of known-container-variables.
Given $O = \{M,S\}; M = \{ok\}; S = \{x,y,z\}$
then we have mappings:
\begin{eqnarray*}
   ok &\mapsto& \seqof{M,O}
\\ x &\mapsto& \seqof{S,O}
\\ y &\mapsto& \seqof{S,O}
\\ z &\mapsto& \seqof{S,O}
\end{eqnarray*}
Perhaps we use this mapping to work from the candidate variables
to possible known pattern variables?
Can this mapping be built incrementally over a list of \texttt{VarTable}s?
}

\begin{code}
vsFreeMatch :: (MonadPlus mp, MonadFail mp)
              => [VarTable] -> TypCmp -> Binding
              -> CBVS -> PBVS
              -> VarSet -> VarSet
              -> mp Binding
vsFreeMatch vts fits bind cbvs pbvs vsC vsP
  = let (uvsP,kvsP,ulsP,klsP) = vsClassify vts vsP in
    if kvsP `withinS` vsC
    then do 
      let kvlC = stdVarsOf (vsC `intsctSl` kvsP)
      let kvlP = stdVarsOf $ S.toList kvsP
      bind' <- bindVarsToVars (zip kvlP kvlC) bind
      let vsC' = vsC `removeS` kvsP
      let klCommonP = klsP `intsctSl` vsC'
      let klCommonC = vsC' `intsctSl` klsP
      bind'' <- bindLVarSTuples
                  ( zip (listVarsOf klCommonP) 
                       $ listVarsOf klCommonC ) bind'
      let klsP' = klsP `removeSl` vsC'
      let vsC'' = S.fromList ((S.toList vsC') `removeL` klCommonP)
      vsKnownMatch vts fits bind'' cbvs pbvs vsC'' (uvsP,ulsP) klsP'
    else fail "vsFreeMatch: known vars missing."
\end{code}

\newpage
A quick std/list-variable classifier:
\begin{code}
vsClassify :: [VarTable] -> VarSet
           -> (VarSet, VarSet, VarSet, VarSet)
vsClassify vts vs
  =  clsfy [] [] [] [] $ S.toList vs
  where
      clsfy uvs kvs uls kls []
        = (S.fromList uvs, S.fromList kvs, S.fromList uls, S.fromList kls)
      clsfy uvs kvs uls kls (s@(StdVar v):gvs)
        = case lookupVarTables vts v of
            UnknownVar  ->  clsfy (s:uvs) kvs uls kls gvs
            _           ->  clsfy uvs (s:kvs) uls kls gvs
      clsfy uvs kvs uls kls (lv@(LstVar (LVbl v _ _)):gvs)
        = case lookupLVarTables vts v of
            UnknownListVar  ->  clsfy uvs kvs (lv:uls) kls gvs
            _               ->  clsfy uvs kvs uls (lv:kls) gvs
\end{code}

\newpage
All known pattern variables have been accounted for,
as well as any pattern list-variables with a direct match.
Now we need to process the remaining known list-variables patterns, if any,
in terms of their expansions.
Here we have two phases:
the first tries to match known list-variables against their immediate
expansions;
the second tries to match them against full expansions.

Unlike the list version above,
where the ordering dictated what should be compared with what,
here we are free to choose any order.
We simply choose to process the remaining pattern list-variables
in order.


\begin{code}
vsKnownMatch :: (MonadPlus mp, MonadFail mp)
              => [VarTable] -> TypCmp -> Binding
              -> CBVS -> PBVS
              -> VarSet
              -> (VarSet, VarSet)
              -> VarList
              -> mp Binding
\end{code}

Simplest case---no more known pattern list-variables
\begin{code}
vsKnownMatch vts fits bind cbvs pbvs vsC (uvsP,ulsP) []
  = vsUnknownMatch vts fits bind cbvs pbvs vsC (uvsP,ulsP)
\end{code}


\begin{code}
-- klsC and kllP are disjoint
vsKnownMatch vts fits bind cbvs pbvs vsC (uvsP,ulsP)
                                (kvP@(LstVar lvP@(LVbl vP _ _)):kslP)
-- lvP is known
  = case expandKnown vts lvP of
      Just (AbstractSet, uis, ujs)
        | kvP `insideS` vsC
          -> do bind' <- bindLVarToVSet lvP (S.singleton kvP) bind
                vsKnownMatch vts fits bind' cbvs pbvs (delS kvP vsC)
                                                 (uvsP,ulsP) kslP
        | otherwise -> fail "vsMatch: abstract lvar only matches self"
      Just kX@(KnownVarSet vsK vsX xSize, uis, ujs)
        | length uis > S.size vsX
          -> fail "vsMatch: invalid known expansion."
        | otherwise
          -> do (bind',vsC1,vsC2)
                  <- vsExpandMatch
                      (vts, lvarClass lvP, varWhen vP)  -- static context
                      (bind, S.empty, S.empty)          -- dynamic context
                      vsC
                      (vsX,uis,ujs,S.size vsX-length uis) -- pattern expansion
                bind'' <- bindLVarToVSet lvP vsC1 bind'
                vsKnownMatch vts fits bind'' cbvs pbvs vsC2 (uvsP,ulsP) kslP
      _ -> fail "vsMatch: pattern-list variable is not set-valued."
{-
    = do
-}
-- vsExpandMatch sctxt@(vts,bc,bw) dctxt@(bind,kappa,ell) vsC xP@(xs,uv,ul,_)
\end{code}

\newpage
\subsection{Known List-Var Expansion Matching (Sets)}

Our expansion clasification devloped above for lists
applies equally well to sets, with cardinality replacing length.


A key metric is the range of possible lengths that an expansion can have:
\begin{eqnarray*}
  range(\setof{v_1,\dots,v_n} \setminus \mathtt{uv} ; \mathtt{ul})
  &=& \left\{
        \begin{array}{lr}
          ~(n-len(\mathtt{uv})), & \mathtt{ul} = \nil
         \\
          ~[0\dots(n-len(\mathtt{uv}))], & \mathtt{ul} \neq \nil
        \end{array}
      \right.
\end{eqnarray*}

First, expansion sets.
\begin{code}
type SExpansion
 = ( Set Variable  --  xs, full expansion less known subtractions
   , [Identifier]  --  uv, subtracted variable identifiers
   , [Identifier]  --  ul, subtracted list-variable identifiers
   , Int           --  size = length xs - length uv
   )
\end{code}


\subsubsection{Matching the set-expansion of a List-Variable.}
We now try to match (all of) \texttt{lvP} incrementally
against a prefix of \texttt{vsC},
using the full expansion, \texttt{vsX} and candidate variables
as we go along.
\begin{eqnarray*}
   expand(\mathtt{lvP})
   &=&
   \setof{vp_1,\dots,vp_m} \setminus \mathtt{uvP} ; \mathtt{ulP}
\\ \mathtt{vsC}
   &=&
   \setof{gc_1,\dots,gc_k,gc_{k+1},\dots,gc_n}
\end{eqnarray*}
If this succeeds, we return a binding between the original \texttt{lvP}
and the corresponding prefix of the original \texttt{vlC},
as well as the remaining suffix of \texttt{vlC}.
\begin{eqnarray*}
   \mathtt{vsC} :: \mathtt{lvP}
   &\leadsto&
   (\mathtt{lvP}\mapsto\setof{gc_1,\dots,gc_k}
   ,\setof{gc_{k+1},\dots,gc_n})
\end{eqnarray*}

We now present a formal description of the algorithm,
by introducing a context that includes bindings, among other things.
We are trying to perform the following partial-match ($\mvs$) inference:
\begin{eqnarray*}
  \dots,\beta
  \vdash
  \setof{gc_1,\dots,gc_k,gc_{k+1},\dots,gc_n} \mvs \mathtt{vlP}
  \leadsto
  (\beta'\override\maplet{\mathtt{vlP}}{\setof{gc_1,\dots,gc_k}},\setof{gc_{k+1},\dots,gc_n})
\end{eqnarray*}
Here $\dots$ denotes further context to be elucidated,
while $\beta'$ indicates that there may be other bindings,
in particular associated with subtracted variables in \texttt{vlP}.
We use $\Gamma$ below to denote the complete context,
and $\gamma,x,y$ to denote context components $x$ and $y$
collected together with $\gamma$, the rest of the context.

We can break the algorithm down into a number of levels
of matching rules:

\begin{tabular}{|c|l|}
\hline
 Symbol & Description
\\\hline
 $\mvs$ & all of pattern list-variable against subset of candidate set
\\\hline
 $\mvsx$ & all of pattern expansion against subset of candidate set
\\\hline
 $\mvsxx$ & subset of pattern expansion against all of candidate expansion
\\\hline
\end{tabular}

The list-based matching is easier because the list-ordering
put a very strong constraint on what needs to match what.
With set-based matching, we have a more general search problem,
as we can pick and choose which bits match.

In the sequel we use $S = T \uplus V$
as a shorthand for $ S = T \cup V \quad\land\quad T \cap V = \emptyset$.

%\adobesucks

\newpage

\subsubsection{Rules for $\mvs$ ---}~

We first start by expanding \texttt{vlP}  as \texttt{xP}
(or \texttt{(xsP,uvP,ulP)}) and using the expansion as the basis
for mapping.
We have a dynamic context $\Gamma=(\beta,\kappa,\ell)$
that evolves as matching progresses,
as well as a static context used for known list-var.
expansion ($expand$), that is not shown below.
The binding passed in, modified and returned
by matching is denoted by $\beta$.
We use $\kappa$
to track the candidate variables matches so far,
and $\ell$  records pattern expansion variables
that will correspond to subtracted pattern list-variables.
\[
\knownSMatchR
\]
%%

\subsubsection{Rules for $\mvsx$ ---}~

\begin{enumerate}
%%%%
\item
The plan with $\mvsx$ is to map successive `subsets' of the \texttt{vlP} expansion
against the expansion of variables, one-by-one in \texttt{vlC}, until
we reduce $\mathtt{xP}$ to `empty'.
The simplest case is when \texttt{vlP} is empty:
\[
\expandSMatchEmptyR
\]
An open question here is what we do with any remaining subtracted
variables in the pattern. They may need to be bound appropriately.
This is the purpose of the $blo$ (bind-leftovers) function.
The $blo$ function for sets satisfies the following specification:
\bloSDef
%%
\item
 When \texttt{vlC} is empty and \texttt{vlP} is inexact,
 we terminate, binding leftovers.
\[
\expandSMatchInExactR
\]
\item
If \texttt{xP} is not empty,
then we match a subset of it against all of the expansion of some chosen
variable in \texttt{vlC}.
If that succeeds then we add the variable to $\kappa$, and recurse.
\[
\expandSMatchNonEmptyR
\]
%%
%%%%
\end{enumerate}



\subsubsection{Rules for $\mvsxx$ ---}~

\begin{enumerate}
%%%%
\item
  We are now using $\mvsxx$ to compare a
  candidate expansion with a pattern expansion,
  trying to match all of the candidate with a subset of the expansion.
  \[
   \Gamma
      \vdash
      \mathtt{xC} \mvsxx \mathtt{xP}
      \leadsto ( \beta',\ell',\mathtt{xP'} )
  \]
  If both are empty, we are done:
\[
\expTwoSMatchAllEmptyR
\]
If the pattern is empty, but the candidate is not, then we fail.
If the candidate is empty, but the pattern is not,
then we return:
\[
\expTwoSMatchCandEmptyR
\]
%%
\item
If both expansions are non-empty,
then we can look for those variables in both, remove them and recurse:
\[
\expTwoSMatchSameR
\]
%%
\item
If the two expansions have no variables in common,
then we need to consider the size-ranges
of both sides to consider what action to take.
If both sides are rigid then the match fails.
The pattern size range must never be smaller than that for the candidate,
for a match to succeed.
In either case, a variable can only be removed from either side
by offsetting against a subtracted unknown variable from the
corresponding side, which is therefore itself also removed.
This action of removing a chosen expansion variable,
and an offsetting subtracted variable is called `shrinking'.`
Any such removal on the pattern side must bind that subtracted variable
to the removed expansion variable, noting that the subtracted variable
may have already been bound in a wider matching context.
\par
In effect we determine conditions for which it is valid
to remove either a candidate or pattern variable.
If both can be removed, then we allow a non-deterministic choice
between which one we do.
%%
\item
We can always shrink an non-rigid non-empty candidate expansion
when \texttt{uvC} is non-null:
\[
\expTwoSMatchClipCandR
\]
%%
\item
We can always shrink an non-rigid non-empty pattern expansion
when \texttt{uvP} is non-null:
\[
\expTwoSMatchClipPatnR
\]
%%
\item
When \texttt{xC} is inexact, and \texttt{uvC} is nil
we can simply remove an arbitrary candidate expansion variable,
but leave \texttt{ulC} untouched.
We do not care which members of \texttt{ulC} cover which members
of the candidate expansion list.
\[
\expTwoSMatchSqueezeCR
\]
Reminder: we can never shrink the candidate if it is rigid.
%%
\item
When \texttt{xP} is inexact, and \texttt{uvP} is nil,
and the pattern size is greater than that of the candidate,
then we can remove an arbitrary pattern expansion variable.
However we must record its removal, so that at the end,
we can decide how to map the members of \texttt{ulP}
to all pattern variables removed in this way.
The record of all such variables is held in the $\ell$
components of the context.
\[
\expTwoSMatchSqueezePR
\]

Reminder: we can never shrink the pattern if it is rigid.
%%%%
\end{enumerate}






\newpage
\begin{code}
vsExpandMatch :: (MonadPlus mp, MonadFail mp)
              => ( [VarTable], VarClass, VarWhen ) -- static context
              -> ( Binding, VarSet, Set Variable )  -- dynamic context
              -> VarSet -- candidate variable list.
              -> SExpansion  -- pattern list-variable expansion
              -> mp ( Binding  -- resulting binding
                    , VarSet  -- matched candidate prefix
                    , VarSet  -- remaining candidate suffix
                    )
\end{code}


\[
\expandSMatchEmptyR
\]
\[
\expandSMatchInExactR
\]
\[
\expandSMatchNonEmptyR
\]

\begin{code}
vsExpandMatch sctxt@(vts,bc,bw) dctxt@(bind,kappa,ell) vsC xP@(xs,uv,ul,_)
  | emptyE xP || (inexactE xP && null vsC)
     = do bind' <-  bindLeftOvers sctxt bind ellxs uv ul
          return (bind',kappa,vsC)
  | not $ null vsC
     =  let (vC,vsC') = choose vsC in
        do xC <- expand vC
           (bind',ell',xP') <- vsExpand2Match sctxt dctxt xC xP
           vsExpandMatch sctxt (bind',S.insert vC kappa,ell') vsC' xP'
  | otherwise = fail "vlExpandMatch: null candidate for exact, non-empty pattern."

  where
    ellxs = S.toList (ell `S.union` xs)
    expand (StdVar v)  = return (S.singleton v,[],[],1)
    expand (LstVar lv)
      = case expandKnown vts lv of
          Just (KnownVarSet vlK vlX _,uis, ujs)
            -> return (vlX,uis,ujs,length vlX - length uis)
          _ ->  fail "vlExpandMatch: candidate is unknown list-var."
\end{code}

\newpage
\begin{code}
vsExpand2Match :: (MonadPlus mp, MonadFail mp)
               => ( [VarTable], VarClass, VarWhen ) -- static context
               -> ( Binding, VarSet, Set Variable )  -- dynamic context
              -> SExpansion  -- candidate variable expansion
              -> SExpansion  -- pattern list-variable expansion
              -> mp ( Binding  -- resulting binding
                    , Set Variable  -- subtracted parts of candidate expansion
                    , SExpansion   -- remaining pattern expansion
                    )
\end{code}

\[
\expTwoSMatchAllEmptyR
\qquad
\expTwoSMatchCandEmptyR
\]

\begin{code}
vsExpand2Match _ dctxt@(bind,_,ell) xC xP
 | emptyE xC  =  return (bind,ell,xP)
\end{code}

\[
\expTwoSMatchSameR
\]
\begin{code}
vsExpand2Match sctxt dctxt xC@(xsC,uvC,ulC,szC) xP@(xsP,uvP,ulP,szP)
  | vC `dvEq` vP  =  vsExpand2Match sctxt dctxt (xsC',uvC,ulC,szC-1)
                                            (xsP',uvP,ulP,szP-1)
  | otherwise
      =  vsShrinkCandMatch sctxt dctxt xC xP
         `mplus`
         vsShrinkPatnMatch sctxt dctxt xC xP
  where
    (vC,xsC') = choose xsC
    (vP,xsP') = choose xsP
\end{code}
\textbf{Note: }\textsl{
Could this code produce ``doubled-up'' matches?
}

\[
\expTwoSMatchSqueezeCR
\]
\[
\expTwoSMatchClipCandR
\]

\begin{code}
vsShrinkCandMatch sctxt dctxt xC@(xsC,uvC,ulC,szC) xP
  | null uvC && null ulC
    = fail "vsShrinkCandMatch: cannot shrink rigid candidate expansion"
  | null uvC -- && not (null ulC)
     = vsExpand2Match sctxt dctxt (xsC',uvC,ulC,szC-1) xP
  | otherwise -- not (null uvC)
     = vsExpand2Match sctxt dctxt (xsC',tail uvC,ulC,szC) xP
  where
    (vC,xsC') = choose xsC
\end{code}

\newpage
\[
\expTwoSMatchSqueezePR
\]
\[
\expTwoSMatchClipPatnR
\]
\begin{code}
vsShrinkPatnMatch sctxt@(_,bc,bw) (bind,gamma,ell)
                  xC@(_,_,_,szC) xP@(xsP,uvP,ulP,szP)
  | null uvP && null ulP
    = fail $ unlines
        [ "vsShrinkPatnMatch: cannot shrink rigid pattern expansion"
        , "xC = " ++ show xC
        , "xP = " ++ show xP
        , "bind:", show bind ]
  | null uvP && szP > szC -- && not null (ulP)
    = vsExpand2Match sctxt (bind,gamma,S.insert vP ell) xC (xsP',uvP,ulP,szP-1)
  | not (null uvP)
     = do vu <- select bind vP Nothing uvP
          bind' <- bindVarToVar vu vP bind
          vsExpand2Match sctxt (bind',gamma,S.insert vP ell) xC (xsP',uvP,ulP,szP)
  | otherwise = fail "vsShrinkPatnMatch: match fail."
  where
    (vP,xsP') = choose xsP

    select bind vP Nothing []  = fail "vlShrinkPatnMatch: no suitable vu found."
    select bind vP (Just vu) []  = return vu
    select bind vP mvu (ui:uvP)
     = let vu = Vbl ui bc bw in
         case lookupVarBind bind vu of
           Nothing -> select bind vP (upd mvu vu) uvP
           Just (BindVar x)
             -- x `dEq` vP ???
             | x == vP    ->  return vu
             | otherwise  ->  select bind vP mvu uvP
           _ -> fail "vsShrinkPatnMatch: subtracted var bound to term."

    upd Nothing x = Just x
    upd mx      _ = mx
\end{code}

\newpage

All that now remains is to match unknown patterns
against the leftover candidates.
We have the following constraints of the sizes of the pattern
and candidate sets:
\begin{itemize}
  \item
    Candidates can be split into standard and list variables.
    \[ vsC = stdC \uplus lstC \]
  \item
    More candidate standard variables than pattern standard variables.
    \[ \#uvsP \leq \#stdC \]
  \item
    If there are no pattern list variables, then
    \[ \#ulsP = 0 \implies \dots \]
    \begin{itemize}
      \item
        we have the same number of candidate and pattern standard variables,
        \[ \#uvsP = \#stdC \]
      \item
        and no candidate list variables.
        \[ lstC = \emptyset \]
    \end{itemize}
\end{itemize}
\textbf{Note: }\textsl{
 This is the match-feasibility criterion again !!!!
}

\begin{code}
vsUnknownMatch :: (MonadPlus mp, MonadFail mp)
               => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
               -> VarSet
               -> (VarSet, VarSet)
               -> mp Binding
vsUnknownMatch vts fits bind cbvs pbvs vsC (uvsP,ulsP)
 | S.size ulsP == 0 && (uvsPs < stdCs || S.size lstC > 0)
   = fail $ unlines
       [ "vsUnknownMatch: not enough general pattern variables"
       , "vsC  = " ++ show vsC
       , "uvsP = " ++ show uvsP
       , "ulsP = " ++ show ulsP
       , "bind:", show bind ]
 | uvsPs > stdCs
   = fail "vsUnknownMatch: not enough standard candidate variables"
 | otherwise
   -- could add non-determinism here.
   = do let (stdC1,stdC2) = splitAt uvsPs $ S.toList stdC
        bind' <- bindVarsToVars (zip (stdVarsOf $ S.toList uvsP)
                                     (stdVarsOf stdC1)) bind
        let vlC = (stdC2 ++ S.toList lstC)
        let ullP = (listVarsOf $ S.toList ulsP)
        ( vsUnkLVarOneEach bind' vlC ullP
        --  `mplus`  -- ***** exists matching bug here ????
        --  vsUnkLVarOneForAll vts bind' cbvs pbvs vlC ullP 
         )
 where
   uvsPs = S.size uvsP
   (uvsC,kvsC,ulsC,klsC) = vsClassify vts vsC
   stdC = uvsC `S.union` kvsC
   stdCs = S.size stdC
   lstC = ulsC `S.union` klsC
\end{code}
\textbf{Note: }\textsl{
More potential for ``doubling-up'' matches?
}

\newpage
We have some unknown pattern list-variables to match
against remaining general candidate variables.
One approach is to bind a chosen pattern list-variable
to all the candidates, with the remaining patterns bound to
the empty list.
Here we return the bindings for all possible choices.
\begin{code}
vsUnkLVarOneForAll :: (MonadPlus mp, MonadFail mp)
               => [VarTable] -> Binding -> CBVS -> PBVS
               -> [GenVar] -> [ListVar]
               -> mp Binding
vsUnkLVarOneForAll vts bind cbvs pbvs vlC [] = return bind
vsUnkLVarOneForAll vts bind cbvs pbvs vlC ullP
  = do emptybs <- bindLVarsToEmpty bind ullP
       updateToAll emptybs (S.fromList vlC) ullP

updateToAll :: (MonadPlus mp, MonadFail mp)
            => Binding -> Set GenVar -> [ListVar] -> mp Binding
-- [ListVar] is not null
updateToAll bind vsC [lvP] = overrideLVarToVSet lvP vsC bind
updateToAll bind vsC (lvP:ullP)
  = ( overrideLVarToVSet lvP vsC bind
      `mplus`
      updateToAll bind vsC ullP )
\end{code}

Here we bind one pattern to one candidate
(currently in list order),
with the following exceptions:
\begin{itemize}
  \item
    If the candidate list is too short,
    then the ``unmatched'' patterns are bound to the empty list.
  \item
    If the candidate-list is too long,
    then the last pattern is bound to all the remaining candidates.
\end{itemize}
\begin{code}
vsUnkLVarOneEach :: MonadFail m
                 => Binding -> [GenVar] -> [ListVar]
                 -> m Binding
vsUnkLVarOneEach bind [] [] = return bind
vsUnkLVarOneEach bind _ [] = fail "no pattern lvars to match remaining cands."
vsUnkLVarOneEach bind vlC [lvP]  = bindLVarToVSet lvP (S.fromList vlC) bind
vsUnkLVarOneEach bind [] ullP  = bindLVarsToEmpty bind ullP
vsUnkLVarOneEach bind (vC:vlC) (lvP:ullP)
  = do bind' <- bindLVarToVSet lvP (S.fromList [vC]) bind
       vsUnkLVarOneEach bind' vlC ullP
\end{code}
\textbf{Note: }\textsl{
 Under what conditions do the above two matches overlap?
}

\newpage
\section{Substitution Matching}

We will write a substitution of the form
$$
  [ e_1,\dots,e_m,\lst e_1,\dots,\lst e_n
  / v_1,\dots,v_m,\lst v_1,\dots,\lst v_n
  ]
$$
in explicit substitution pair form as two sets of such tuples:
$$
 \{ e_1/v_1 , \dots e_m/v_m \}
 \quad
 \{ \lst e_1/\lst v_1 , \dots \lst e_n/\lst v_n \}
$$
Note that the $v_i$ and $\lst v_j$ need to be unique.

We will then distinguish pattern ($P$) from candidate ($C$)
by using $e_{Pi}$ and $e_{Ci}$.

So the substitution pattern match problem is:

\hrule

\begin{eqnarray*}
     \{ e_{C1}/v_{C1} , \dots e_{Cp}/v_{Cp} \}
     &\quad&
     \{ \lst e_{C1}/\lst v_{C1} , \dots \lst e_{Cq}/\lst v_{Cq} \}
\\ & :: &
\\   \{ e_{P1}/v_{P1} , \dots e_{Pm}/v_{Pm} \}
     &\quad&
     \{ \lst e_{P1}/\lst v_{P1} , \dots \lst e_{Pn}/\lst v_{Pn} \}
\end{eqnarray*}

\hrule

This an instance of a ``collection'' match (\textsection\ref{ssec:coll-matching})
so the feasibility constraints given there apply:
\begin{code}
isFeasibleSubstnMatch :: Substn -> Substn -> Bool
isFeasibleSubstnMatch (Substn tsC lvsC) (Substn tsP lvsP)
  = let m = S.size tsP
        n = S.size lvsP
        p = S.size tsC
        q = S.size lvsC
    in isFeasibleCollMatch(m,n,p,q)
\end{code}
If the match succeeds, then the resulting binding needs to contain:
\begin{itemize}
  \item  $e_{Pi} \mapsto e_{Cj}, v_{Pi} \mapsto v_{Cj}$,
    \\for all $i \in 1\dots m$, and $m$ values of $j$ drawn from $1\dots p$;
  \item
     $ \lst e_{Pk}  \mapsto
          \seqof{\dots,e_{C\ell},\dots;\dots \lst e_{C\ell}\dots}$
    \\ $ \lst v_{Pk} \mapsto
            \seqof{\dots,v_{C\ell},\dots;\dots \lst v_{C\ell}\dots}$
    \\for $k \in 1\dots n$, and values of $\ell$ disjoint from the $j$ above.
\end{itemize}
Here $G$ denotes either one standard variable,
or a collection of general variables,
while $g$ denotes one general variable.
Similarly, $r$ denotes one substitution replacement (list-variable or term)
while $R$ is a collection of same.
$$
\inferrule
   { \beta \vdash G_{C_j} :: g_{P_i} \leadsto \beta_{t_i}
     \and
     \beta \uplus \{\beta_{t_i}\} \vdash R_{C_j} :: r_{P_i} \leadsto \beta_{r_i}
   }
   { \beta \vdash [R_{C_j}/G_{C_j}]_j :: [r_{P_i}/g_{P_i}]_i
     \leadsto
     \uplus \{\beta_{t_i}\uplus\beta_{r_i}\}
   }
   \quad
   \texttt{sMatch}
$$
\begin{code}
sMatch :: (MonadPlus mp, MonadFail mp)
       => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
       -> Substn -> Substn
       -> mp Binding
sMatch vts fits bind cbvs pbvs subC subP
  | isFeasibleSubstnMatch subC subP  =  sMatch' vts fits bind cbvs pbvs subC subP
  | otherwise                        =  fail "infeasible substition match"
\end{code}

We match substitutions by first trying every way
to match pattern (variable,term) pairs
against their candidate counterparts.
For each outcome, we then try to match the list-variables pairs
against what remains.
\begin{code}
sMatch' vts fits bind cbvs pbvs subC@(Substn tsC lvsC) subP@(Substn tsP lvsP)
 = do (bind',tsC')  <- vtsMatch vts fits bind cbvs pbvs tsC tsP
      lvsMatch vts fits bind' cbvs pbvs tsC' (S.toList lvsC) (S.toList lvsP)
\end{code}

\subsection{Substitution Term/Variable matching}

Matching
$\{ e_{C1}/v_{C1} , \dots e_{Cp}/v_{Cp} \}$
against
$\{ e_{P1}/v_{P1} , \dots e_{Pm}/v_{Pm} \}$
in every way possible,
returning leftover $\{e_{Ci}/v_{Ci}\}$s.

We expect bindings of the form
 $e_{Pi} \mapsto e_{Cj}, v_{Pi} \mapsto v_{Cj}$,
for all $i \in 1\dots m$, and $m$ values of $j$ drawn from $1\dots p$;
\begin{code}
vtsMatch :: (MonadPlus mp, MonadFail mp)
         => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
         -> TermSubs -> TermSubs
         -> mp (Binding,[(Variable,Term)])
vtsMatch vts fits bind cbvs pbvs tsC tsP
 = manyToMultiple (matchPair matchVar matchTerm) defCombine id
              (S.toList tsC) (S.toList tsP) bind
 where
   matchVar :: (MonadPlus mp, MonadFail mp) 
            => BasicM mp Binding Variable Variable
   matchVar vC vP bind = vMatch vts fits bind cbvs pbvs ArbType vC ArbType vP
   matchTerm :: (MonadPlus mp, MonadFail mp) 
             => BasicM mp Binding Candidate Pattern
   matchTerm tC tP bind =  termMatch vts fits bind cbvs pbvs tC tP
\end{code}

\newpage
\subsection{Substitution ListVar Matching}

We are now matching
\begin{eqnarray*}
     \{ e_{C1}/v_{C1} , \dots e_{Cr}/v_{Cr} \}
     &\quad&
     \{ \lst e_{C1}/\lst v_{C1} , \dots \lst e_{Cq}/\lst v_{Cq} \}
\\ & :: &
\\   \{  \}
     &\quad&
     \{ \lst e_{P1}/\lst v_{P1} , \dots \lst e_{Pn}/\lst v_{Pn} \}
\end{eqnarray*}
where $r$ is the number of term/var candidates
not matched by term/var patterns ($r = p-m$).

We expect bindings of the form
$ \lst e_{Pk}  \mapsto
          \seqof{\dots,e_{C\ell},\dots;\dots \lst e_{C\ell}\dots}$
and
$ \lst v_{Pk} \mapsto
            \seqof{\dots,v_{C\ell},\dots;\dots \lst v_{C\ell}\dots}$
for $k \in 1\dots n$.

For now we produce specific cases,
and leave a general solution for later.
\begin{code}
lvsMatch :: (MonadPlus mp, MonadFail mp)
       => [VarTable] -> TypCmp -> Binding -> CBVS -> PBVS
       -> [(Variable,Term)] -> [(ListVar,ListVar)] -> [(ListVar,ListVar)]
       -> mp Binding

lvsMatch vts fits bind cbvs pbvs [] [] [] = return bind
lvsMatch vts fits bind cbvs pbvs _  _  [] = fail "lvsMatch: no patn. for candidates."
\end{code}

One pattern element only is easy
\begin{eqnarray*}
     \{ e_{C1}/v_{C1} , \dots e_{Cr}/v_{Cr} \}
     &\quad&
     \{ \lst e_{C1}/\lst v_{C1} , \dots \lst e_{Cq}/\lst v_{Cq} \}
\\ & :: &
\\   \{  \}
     &\quad&
     \{ \lst e_{P}/\lst v_{P}  \}
\end{eqnarray*}
We expect
$ \lst e_{P}  \mapsto
          \seqof{e_{C1},\dots;\dots \lst e_{Cr}}$
and
$ \lst v_{P} \mapsto
            \seqof{v_{C1},\dots;\dots \lst v_{Cr}}$.
\begin{code}
lvsMatch vts fits bind cbvs pbvs tsC lvsC [(vsP,esP)]
  = do bind' <- bindLVarToVList vsP cTgts bind
       bindLVarSubstRepl esP cLVTs bind'
  where
    cVars = map fst tsC ; cTgtL = map fst lvsC
    cTgts = (map StdVar cVars ++ map LstVar cTgtL)
    cTerms = map snd tsC ; cRplL = map snd lvsC
    cLVTs = map Right cTerms ++ map Left cRplL
\end{code}
Next case, candidate is only list variables:
\begin{code}
lvsMatch vts fits bind cbvs pbvs [] lvsC lvsP -- = fail "lvsMatch [] lvsC lvsP NYI"
 = do (bind',lvsC') <- manyToMultiple (matchPair matchLVar matchLVar)
                                          defCombine id lvsC lvsP bind
      return bind'
 where
   matchLVar  ::  (MonadPlus mp, MonadFail mp) => BasicM mp Binding ListVar ListVar
   matchLVar lvC lvP bind = vsMatch vts fits bind cbvs pbvs
                                    (S.singleton $ LstVar lvC)
                                    (S.singleton $ LstVar lvP)
\end{code}
Right now my head hurts.
\begin{code}
lvsMatch vts fits bind cbvs pbvs tsC lvsC lvsP
  = fail $ unlines'
      [ "lvsMatch NYfI"
      , "@tsC: "++show tsC
      , "@lvsC: "++show lvsC
      , "@lvsP: "++show lvsP
      , "@bind: "++show bind
      ]
\end{code}
