\section{Matching}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Matching
( match
, tMatch, tsMatch
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
import LexBase
import Variables
import AST
import VarData
import Binding

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

\subsection{Matching Principles}

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
\subsection{Haskell Types for Matching}

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

\subsection{Top-level Matching}

At the top-level we have the known-variable information
in the form of a sequence $\kappa s$ of known variable tables,
and the pattern and candidate terms,
and we hope to get at least one binding.
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
match :: MonadPlus mp => [VarTable] -> Candidate -> Pattern -> mp Binding
match vts c p  =  tMatch vts emptyBinding noBVS noBVS c p
\end{code}

\subsection{Term Matching}

\begin{code}
tMatch, tMatch' ::
  MonadPlus mp => [VarTable] -> Binding -> CBVS -> PBVS
               -> Candidate -> Pattern -> mp Binding
\end{code}

We note that the \texttt{TermKind} of pattern and candidate must match.
Either both are predicates,
or both are expressions with the type of the candidate
being an sub-type of the pattern.
\begin{code}
tMatch vts bind cbvs pbvs tC tP
 = case (termkind tC, termkind tP) of
    (P,P)                       ->  tMatch' vts bind cbvs pbvs tC tP
    (E typC, E typP)
      | typC `isSubTypeOf` typP   ->  tMatch' vts bind cbvs pbvs tC tP
    _ -> fail "tMatch: incompatible termkinds."
\end{code}

Term-matching is defined inductively over the pattern type.

We start with the simple value and structural composite matches,
and then proceed to look at variable, binder and substitution patterns.

\subsubsection{Value Term-Pattern (\texttt{Val})}
Values only match themselves.
$$
\inferrule
   {{\kk k}_C = {\kk k}_P}
   {\beta \vdash {\kk k}_C :: {\kk k}_P \leadsto \beta}
   \quad
   \texttt{tMatch Val}
$$
\begin{code}
tMatch' _ bind _ _ kC@(Val _ _) kP@(Val _ _)
 | kC == kP  =  return bind
\end{code}

\subsubsection{Variable Term-Pattern (\texttt{Var})}
Variable matching is complicated, so we farm it out,
as long as \texttt{TermKind}s match.
$$
\inferrule
   {\beta \vdash t_C :: v_P \leadsto \beta'}
   {\beta \vdash t_C :: {\vv v}_P \leadsto \beta'}
   \quad
   \texttt{tMatch Var}
$$
\begin{code}
tMatch' vts bind cbvs pbvs tC (Var tkP vP)
  | tkP == termkind tC  =  tvMatch vts bind cbvs pbvs tC tkP vP
\end{code}


\subsubsection{Constructor Term-Pattern (\texttt{Cons})}
Constructors match if they have the same name and kind
and the term-lists are of the same length and corresponding terms match.
$$
\inferrule
   { n_C = n_P
     \and
     \beta \vdash t_{C_i} :: t_{P_i} \leadsto \beta_i
   }
   {\beta \vdash \cc{n_C}{ts_C} :: \cc{n_P}{ts_P} \leadsto \uplus\{\beta_i\}}
   \quad
   \texttt{tMatch Cons}
$$
Here $ts_X = \langle t_{X_1}, t_{X_2}, \dots t_{X_n} \rangle$.
\begin{code}
tMatch' vts bind cbvs pbvs (Cons tkC nC tsC) (Cons tkP nP tsP)
 | tkC == tkP && nC == nP  =  tsMatch vts bind cbvs pbvs tsC tsP
\end{code}

\subsubsection{Binding Term-Pattern (\texttt{Bind})}

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
   \texttt{tMatch Binding}
$$
\begin{code}
tMatch' vts bind cbvs pbvs (Bind tkC nC vsC tC) (Bind tkP nP vsP tP)
  | tkP == tkC && nC == nP
    =  do let cbvs' = vsC `addBoundVarSet` cbvs
          let pbvs' = vsP `addBoundVarSet` pbvs
          bindT  <-  tMatch vts bind cbvs' pbvs' tC tP
          vsMatch vts bindT cbvs' pbvs' vsC vsP
\end{code}

\subsubsection{Lambda Term-Pattern (\texttt{Lam})}

$$
\inferrule
   {n_C = n_P
    \and
    \beta;(B_C\cup vs_C,B_P\cup vs_P) \vdash t_C :: t_P \leadsto \beta'_t
    \and
    \beta \vdash vl_C :: vl_P \leadsto \beta'_{vl}
   }
   { \beta;(B_C,B_P) \vdash \ll{n_C}{vl_C}{t_C} :: \ll{n_P}{vl_P}{t_P}
     \leadsto
     \beta \uplus \beta'_t \uplus \beta'_{vl}
   }
   \quad
   \texttt{tMatch Binding}
$$
\begin{code}
tMatch' vts bind cbvs pbvs (Lam tkC nC vlC tC) (Lam tkP nP vlP tP)
  | tkP == tkC && nC == nP
    =  do let cbvs' = vlC `addBoundVarList` cbvs
          let pbvs' = vlP `addBoundVarList` pbvs
          bindT  <-  tMatch vts bind cbvs' pbvs' tC tP
          vlMatch vts bindT cbvs' pbvs' vlC vlP
\end{code}


\subsubsection{Substitution Term-Pattern (\texttt{Sub})}

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
   \texttt{tMatch Subst}
$$
\begin{code}
tMatch' vts bind cbvs pbvs (Sub tkC tC subC) (Sub tkP tP subP)
  | tkP == tkC
    =  do bindT  <-  tMatch vts bind cbvs pbvs tC tP
          sMatch vts bindT cbvs pbvs subC subP
\end{code}


\subsubsection{Iterated Term-Pattern (\texttt{Iter})}

$$
\inferrule
   {na_C = na_P \and ni_C = ni_P
    \and \#lvs_C = \#lvs_P
   }
   { \beta \vdash \ii{na_C}{ni_C}{lvs_C} :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus \beta \uplus \{lvs_P[i] \mapsto lvs_C[i]\}_{i \in 1\dots\#lvs_P}
   }
   \quad
   \texttt{tMatch Iter-Self}
$$

\begin{code}
tMatch' vts bind cbvs pbvs (Iter tkC naC niC lvsC) (Iter tkP naP niP lvsP)
  | tkP == tkC && naC == naP && niC == niP && length lvsP == length lvsC
               =  ibind bind $ zip lvsP lvsC
  | otherwise  =  fail "tMatch: incompatible Iter."
  where
    ibind bind [] = return bind
    ibind bind ((lvP,lvC):rest)
      = do bind' <- bindLVarToVList lvP [LstVar lvC] bind
           ibind bind' rest
\end{code}

Plus a more complicated rule:
$$
\inferrule
   {na_C = na_P \and ni_C = ni_P
   \and
   \and j \in 1 \dots\#\seqof{t_C}
   \and
   \#(\seqof{t_{C}}[j]) = \#lvs_P
   }
   { \beta \vdash na_C(ni_C\seqof{t_C}_j) :: \ii{na_P}{ni_P}{lvs_P}
     \leadsto
     \beta \uplus \{lvs_P[i] \mapsto \seqof{t_C[i]}_j\}_{i \in 1\dots\#lvs_P}
   }
   \quad
   \texttt{tMatch Iter-Cons}
$$

\begin{code}
tMatch' vts bind cbvs pbvs tC@(Cons tkC naC tsC) (Iter tkP naP niP lvsP)
  | tkP == tkC && naC == naP && all isNiP tsC
               = ibind bind $ zip lvsP $ transpose $ map unNiP tsC
  | otherwise
     = fail $ unlines
         [ "tMatch: Cons not compatible with Iter."
         , "tkP  = " ++ show tkP
         , "tkC  = " ++ show tkC
         , "naP  = " ++ show naP
         , "naC  = " ++ show naC
         , "niP  = " ++ show niP
         , "lvsP = " ++ show lvsP
         , "tsC  = " ++ show tsC
         ]
  where
    arity = length lvsP
    isNiP (Cons _ n ts)  =  n == niP && length ts == arity
    isNiP _              =  False
    unNiP (Cons _ _ ts)  =  ts
    unNiP _              =  []
    ibind bind [] = return bind
    ibind bind ((lvP,tsC):rest)
      =  do bind' <- bindLVarToTList lvP tsC bind
            ibind bind' rest
\end{code}

Any other case results in failure:
\begin{code}
tMatch' _ _ _ _ tC tP
 = fail $ unlines
    [ "tMatch: structural mismatch."
    , "tC = " ++ show tC
    , "tP = " ++ show tP
    ]
\end{code}

\subsection{Term-List Matching}

For now a simple zip-like walk along both lists
(no precomputing length to abort early).
\begin{code}
tsMatch :: MonadPlus mp
        => [VarTable] -> Binding -> CBVS -> PBVS
        -> [Candidate] -> [Pattern] -> mp Binding
tsMatch _ _ _ _ cts pts
 | length cts /= length pts = fail "tsMatch: length mismatch"
tsMatch _ bind _ _ [] [] = return bind
tsMatch vts bind cbvs pvbs (tC:tsC) (tP:tsP)
 = do bind1 <- tMatch vts bind cbvs pvbs tC tP
      tsMatch vts bind1 cbvs pvbs tsC tsP
-- should not occur!
tsMatch _ _ _ _ _ _  =  error "tsMatch: unexpected mismatch case."
\end{code}


\newpage
\subsection{Term-Variable Matching}

We assume here that candidate term and pattern variable
had the same \texttt{TermKind}.
\begin{code}
tvMatch :: Monad m
       => [VarTable] -> Binding -> CBVS -> PBVS
       -> Candidate -> TermKind -> Variable -> m Binding
\end{code}

First, if the candidate is a variable
we go to do variable-on-variable matching:
\begin{code}
tvMatch vts bind cbvs pbvs (Var tkC vC) tkP vP
  = vMatch vts bind cbvs pbvs vC vP
\end{code}

Otherwise we check if the pattern is
bound, known, or arbitrary,
and act accordingly.
\begin{code}
tvMatch vts bind cbvs pvbs tC tkP vP@(Vbl _ _ vt)
 | vt == Textual              =  fail "tvMatch: var-variable cannot match term."
 | StdVar vP `S.member` pvbs  =  fail "tvMatch: bound pattern cannot match term."
 | vPmr /= UnknownVar         =  tkvMatch vts bind tC vPmr tkP vP
\end{code}
\subsubsection{Arbitrary Pattern Variable}
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
--tvMatch vts bind cbvs pvbs tC tkP vP@(Vbl _ vw _)
 | otherwise                  =  bindVarToTerm vP tC bind
 where
   vPmr = lookupVarTables vts vP
\end{code}

\newpage
\subsubsection{Known Pattern Variable}

\begin{code}
tkvMatch :: Monad m => [VarTable] -> Binding
       ->  Candidate -> VarMatchRole -> TermKind -> Variable -> m Binding
-- know vP is not in pbvs, in vts, and it maps to whatP
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
-- know vP is not in pbvs, in vts, and it maps to whatP
tkvMatch vts bind tC@(Var _ vC) whatP tkP vP
 | vC == vP                                    =  bindVarToVar vP vP bind
 | isKnownConst whatP && tC == vmrConst whatP  =  bindVarToVar vP vC bind
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
-- know vP is not in pbvs, in vts, and it maps to whatP
tkvMatch vts bind tC whatP tkP vP
 | isKnownConst whatP && tC == vmrConst whatP     =  bindVarToTerm vP tC bind
 | isExprKind tkP && isKnownVar whatP
   && vmrType whatP == ekType tkP                 =  bindVarToTerm vP tC bind
tkvMatch _ _ _ _ _ _ = fail "tkvMatch: candidate not this known variable."
\end{code}

\newpage
\subsection{Variable Matching}

The rules regarding suitable matches for pattern variables
depend on what class of variable we have (\texttt{VarWhat})
and what we know about them (\texttt{VarMatchRole}).

First, rules based on classification:

\begin{tabular}{|c|c|c|}
\hline
Class & \texttt{VarWhat} & Allowed Candidates
\\\hline
 Observation & \texttt{ObsV} & Observation, Expression
\\\hline
 Variable & \texttt{VarV} & Variable
\\\hline
 Expression & \texttt{ExprV} & Expression
\\\hline
  Predicate & \texttt{PredV} & Predicate
\\\hline
\end{tabular}

Next, rules based on knowledge:

\begin{tabular}{|c|c|c|}
\hline
Knowledge & \texttt{VarMatchRole} & Allowed Candidates
\\\hline
Unknown & \texttt{UnknownVar} & Anything as per classification.
\\\hline
Known variable & \texttt{KnownVar} & Itself only
\\\hline
Known constant & \texttt{KnownConst} & Itself or the constant
\\\hline
\end{tabular}

Finally, rules based on the static or dynamic nature of known variables,
that do not apply if the variable is bound.
\begin{itemize}
  \item Static variables can match static or dynamic variables.
  \item Dynamic variables can only match those that have the
  same \texttt{VarWhen} value,
  except that the string in \texttt{During} may differ.
\end{itemize}
\begin{code}
whenCompVar :: Variable -> Variable -> Bool
whenCompVar (Vbl _ _ vkC) (Vbl _ _ vkP) = whenCompKind vkC vkP

whenCompKind :: VarWhen -> VarWhen -> Bool  -- candidate, pattern
whenCompKind _          Static      =  True
whenCompKind Textual    Textual     =  True
whenCompKind Before     Before      =  True
whenCompKind (During _) (During _)  =  True
whenCompKind After      After       =  True
whenCompKind _          _           =  False
\end{code}

Now, onto variable matching:

\begin{code}
vMatch :: Monad m
       => [VarTable] -> Binding -> CBVS -> PBVS
       -> Variable -> Variable
       -> m Binding
\end{code}

Observation pattern variables may match either
observation or expression variables,
while other variable classes may only match their own class.
\begin{code}
vMatch vts bind cbvs pvbs vC@(Vbl _ vwC _) vP@(Vbl _ vwP _)
 | StdVar vP `S.member` pvbs    =  bvMatch vts bind cbvs vC vP
 | vC == vP                     =  bindVarToVar vP vC bind
 | vwC == vwP                   =  vMatch' (lookupVarTables vts vP) vC vP
 | vwC == ExprV && vwP == ObsV  =  vMatch' (lookupVarTables vts vP) vC vP
 | otherwise                    =  fail "vMatch: class mismatch"
 where
\end{code}

Variable classes are compatible, but is the pattern ``known''?
\begin{code}
  -- vC /= vP
  vMatch' UnknownVar vC vP               =  bindVarToVar vP vC bind
  vMatch' (KnownVar typ) vC vP
    | whenCompVar vC vP                  =  bindVarToVar vP vC bind
  vMatch' (KnownConst (Var _ v)) vC vP
    | vC == v                            =  bindVarToVar vP vC bind
  vMatch' _ _ _  =  fail "vMatch: knowledge mismatch."
\end{code}

\subsubsection{Bound Pattern Variable}
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
bvMatch :: Monad m => [VarTable] -> Binding -> CBVS
        -> Variable -> Variable -> m Binding
-- we know vP is in pbvs
bvMatch vts bind cbvs vC@(Vbl _ vwC _) vP@(Vbl _ vwP _)
 | vwC /= vwP  =  fail "bvMatch: variable class mismatch."
 | StdVar vC `S.member` cbvs  =  bindVarToVar vP vC bind
 | otherwise  =  fail "bvMatch: candidate not a bound variable."
\end{code}


\newpage
\subsection{Variable-List Matching}

\begin{code}
vlMatch :: MonadPlus mp => [VarTable] -> Binding -> CBVS -> PBVS
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
vlMatch vts bind cbvs pbvs vlC [] = fail "vlMatch: null pattern."
vlMatch vts bind cbvs pbvs [] vlP = fail "vlMatch: null candidate."
vlMatch vts bind cbvs pbvs vlC vlP
  = do (vlC',vlP') <- applyBindingsToLists bind vlC vlP
       vlFreeMatch vts bind cbvs pbvs vlC' vlP'
\end{code}

\subsubsection{Applying Bindings to Lists}

We simply walk up the pattern looking for variables
already bound, and then search for what they are bound to, in the candidate
list.
We remove both, and continue.

We use tail-recursion and accumulate the un-bound (or ``free'') part of both
lists.
\begin{code}
applyBindingsToLists :: MonadPlus mp
                 => Binding -> VarList -> VarList -> mp (VarList,VarList)
applyBindingsToLists bind vlC vlP
  = applyBindingsToLists' bind [] [] vlC vlP

applyBindingsToLists' :: MonadPlus mp
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
 = case lookupBind bind vP of
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
\paragraph{Find Standard Pattern-Variable Binding}
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

\paragraph{Find List Pattern-Variable Binding}
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
\subsubsection{Free Variable-List Matching}

Here we are doing variable-list matching where all of the
pattern variables are free, \textit{i.e.}, not already in the binding.
We do not attempt a complete solution,
as in fact there can be many possible bindings.
We adopt a heuristic that simply walks the pattern list
from left to right and tries to bind the head pattern variable
against some prefix of the candidate list.
\begin{code}
vlFreeMatch :: MonadPlus mp
              => [VarTable] -> Binding
              -> CBVS -> PBVS
              -> VarList -> VarList
              -> mp Binding
\end{code}

If both lists are empty, we are done:
\begin{code}
vlFreeMatch vts bind cbvs pbvs [] [] = return bind
\end{code}

If there are leftover candidate variables, we fail
\begin{code}
vlFreeMatch vts bind cbvs pbvs vlC []
  = fail "vlMatch: too many candidate variables."
\end{code}

Standard pattern variable matches are easy.
The head of the candidate list must be a pattern variable.
It must also match according to the rules for variable matching.
\begin{code}
vlFreeMatch vts bind cbvs pbvs [] (StdVar vP:_)
  = fail "vlMatch: too many std. pattern variables."

vlFreeMatch vts bind cbvs pbvs ((StdVar vC):vlC) ((StdVar vP):vlP)
  = do bind' <- vMatch vts bind cbvs pbvs vC vP
       vlFreeMatch vts bind' cbvs pbvs vlC vlP

vlFreeMatch vts bind cbvs pbvs vlC ((StdVar _):_)
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
vlFreeMatch vts bind cbvs pbvs vlC (gvP@(LstVar lvP):vlP)
  = let bc = lvarClass lvP in
    case expandKnown vts lvP of
     Nothing
       -> vlFreeMatchN vts bind cbvs pbvs bc vlC lvP vlP 0
          `mplus`
          vlFreeMatchN vts bind cbvs pbvs bc vlC lvP vlP 1
          `mplus`
          vlFreeMatchN vts bind cbvs pbvs bc vlC lvP vlP 2
     Just (AbstractList, uis, ujs)
       | null vlC -> fail "vlMatch: not enough candidates."
       | gvP /= head vlC  ->  fail "vlMatch: abstract lvar. only matches self."
       | otherwise
           -> do bind' <- bindLVarToVList lvP [gvP] bind
                 vlFreeMatch vts bind' cbvs pbvs (tail vlC) vlP
     Just kX@(KnownVarList vlK vlX xLen, uis, ujs)
       | length uis > length vlX
          -> fail "vlMatch: invalid known epxansion"
       | otherwise
          -> do (bind',vlC') <- vlKnownMatch vts bind cbvs pbvs
                                     bc vlC gvP vlK vlX uis ujs
                vlFreeMatch vts bind' cbvs pbvs vlC' vlP
     _ -> fail "vlMatch: pattern list-variable is set-valued."
\end{code}


Returns true if the list variable is unknown,
or known to be an empty \emph{list}.
\begin{code}
canMatchNullList :: [VarTable] -> ListVar -> Bool
canMatchNullList vts lv
  = case lookupLVarTables vts (varOf lv) of
      KnownVarList vl _ _  ->  null vl
      UnknownListVar       ->  True
      _                    ->  False
\end{code}

We have a simple, ``slightly greedy'' algorithm
that matches a list-variable against the first \texttt{n} candidates.
\begin{code}
vlFreeMatchN vts bind cbvs pbvs bc vlC lvP vlP n
 = do bind' <- bindLVarToVList lvP firstnC bind
      vlFreeMatch vts bind' cbvs pbvs restC vlP
 where
    (firstnC,restC)  =  splitAt n vlC
\end{code}

\newpage
\paragraph{Matching a List-Variable, known to be a list.}
First we handle simple cases, where either the list-variable,
its definition, or its expansion as variables,
are a prefix of the candidate list.
\begin{code}
-- not null vlC
vlKnownMatch vts bind cbvs pbvs
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
\end{code}

\newpage
\subsubsection{Known List-Var Expansion Matching}

\paragraph{Classifying Expansions}
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


\paragraph{Matching the list-expansion of a List-Variable.}
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

%\adobesucks

\newpage

\paragraph{Rules for $\mvl$ ---}~

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
\knownMatchR
\]
%%

\paragraph{Rules for $\mvlx$ ---}~

\begin{enumerate}
%%%%
\item
The plan with $\mvlx$ is to map successive `prefixes' of the \texttt{vlP} expansion
against the expansion of variables, one-by-one in \texttt{vlC}, until
we reduce $\mathtt{xP}$ to `empty'.
The simplest case is when \texttt{vlP} is empty:
\[
\expandMatchEmptyR
\]
An open question here is what we do with any remaining subtracted
variables in the pattern. They may need to be bound appropriately.
This is the purpose of the $blo$ (bind-leftovers) function.
The $blo$ function satisfies the following specification:
\bloDef
%%
\item
 When \texttt{vlC} is empty and \texttt{vlP} is inexact,
 we terminate, binding leftovers.
\[
\expandMatchInExactR
\]
\item
If \texttt{xP} is not empty,
then we match a prefix of it against all of the expansion of the first
variable in \texttt{vlC}.
If that succeeds then we add the variable to $\kappa$, and recurse.
\[
\expandMatchNonEmptyR
\]
%%
%%%%
\end{enumerate}



\paragraph{Rules for $\mvlxx$ ---}~

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
\expTwoMatchAllEmptyR
\]
If the pattern is empty, but the candidate is not, then we fail.
If the candidate is empty, but the pattern is not,
then we return:
\[
\expTwoMatchCandEmptyR
\]
%%
\item
If both expansions are non-empty, then we compare the first two variables
in their expansions.
If they are the same, remove both and recurse:
\[
\expTwoMatchSameR
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
\expTwoMatchClipCandR
\]
%%
\item
We can always shrink an non-rigid non-empty pattern expansion
when \texttt{uvP} is non-null:
\[
\expTwoMatchClipPatnR
\]
%%
\item
When \texttt{xC} is inexact, and \texttt{uvC} is nil
we can simply remove the leading candidate expansion variable,
but leave \texttt{ulC} untouched.
We do not care which members of \texttt{ulC} cover which members
of the candidate expansion list.
\[
\expTwoMatchSqueezeCR
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
\expTwoMatchSqueezePR
\]

Reminder: we can never shrink the pattern if it is rigid.
%%%%
\end{enumerate}

\newpage

First, expansions and predicates over them.
\begin{code}
type Expansion
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
\bloDef
We need part of the static context here.
\begin{code}
-- blo to be defined here
bindLeftOvers :: MonadPlus mp
              => ( [VarTable], VarClass, VarWhen ) -- static context
              -> Binding
              -> [Variable]   -- expansion variables ( ell ++ xs)
              -> [Identifier] -- subtracted variables
              -> [Identifier] -- subtracted list-variables
              -> mp Binding
bindLeftOvers (_,bc,bw) bind xs us ls
  = do (bind',xs') <- bloVars bind xs us
       bloLVars bind' xs' ls
  where

    bloVars bind xs []  =  return (bind,xs)
    bloVars bind []  _  =  fail "bindLeftOvers: too few expansion vars."
    bloVars bind xs (ui:us)
      = case lookupBind bind uv of
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
      = bindLVarToVList (LVbl (Vbl ui bc bw) [] []) (map StdVar xs) bind
    bloLVars bind xs (ui:ul)
      = case lookupLstBind bind lv of
         Nothing
           -> do bind' <- bindLVarToVList  lv [] bind
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
vlExpandMatch :: MonadPlus mp
              => ( [VarTable], VarClass, VarWhen ) -- static context
              -> ( Binding, VarList, [Variable] )  -- dynamic context
              -> VarList -- candidate variable list.
              -> Expansion  -- pattern list-variable expansion
              -> mp ( Binding  -- resulting binding
                    , VarList  -- matched candidate prefix
                    , VarList  -- remaining candidate suffix
                    )
\end{code}


\[
\expandMatchEmptyR
\]
\[
\expandMatchInExactR
\]
\[
\expandMatchNonEmptyR
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
vlExpand2Match :: MonadPlus mp
               => ( [VarTable], VarClass, VarWhen ) -- static context
               -> ( Binding, VarList, [Variable] )  -- dynamic context
              -> Expansion  -- candidate variable expansion
              -> Expansion  -- pattern list-variable expansion
              -> mp ( Binding  -- resulting binding
                    , [Variable]  -- subtracted parts of candidate expansion
                    , Expansion   -- remaining pattern expansion
                    )
\end{code}

\[
\expTwoMatchAllEmptyR
\qquad
\expTwoMatchCandEmptyR
\]

\begin{code}
vlExpand2Match _ dctxt@(bind,_,ell) xC xP
 | emptyE xC  =  return (bind,ell,xP)
\end{code}

\[
\expTwoMatchSameR
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

\[
\expTwoMatchSqueezeCR
\]
\[
\expTwoMatchClipCandR
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
\expTwoMatchSqueezePR
\]
\[
\expTwoMatchClipPatnR
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
         case lookupBind bind vu of
           Nothing -> select bind vP (upd mvu vu) uvP
           Just (BindVar x)
             | x == vP    ->  return vu
             | otherwise  ->  select bind vP mvu uvP
           _ -> fail "vlShrinkPatnMatch: subtracted var bound to term."

    upd Nothing x = Just x
    upd mx      _ = mx
\end{code}

\newpage
\subsection{Variable-Set Matching}

We follow a similar pattern to variable-list matching.
First apply any bindings we have, and then try to match what is left.
The key difference here, obviously, is that order does not matter,
and we expect list-variables, if known, to be known as variable-sets,
not lists.
\begin{code}
vsMatch :: MonadPlus mp => [VarTable] -> Binding -> CBVS -> PBVS
        -> VarSet -> VarSet -> mp Binding
-- vsC `subset` cbvs && vsP `subset` pbvc
vsMatch vts bind cbvs pbvc vsC vsP
  = do (vsC',vsP') <- applyBindingsToSets bind vsC vsP
       vsFreeMatch vts bind cbvs pbvc vsC' vsP'
\end{code}

\subsubsection{Applying Bindings to Sets}

\begin{code}
applyBindingsToSets
  :: MonadPlus mp
  => Binding -> VarSet -> VarSet -> mp (VarSet,VarSet)
applyBindingsToSets bind vsC vsP
 = applyBindingsToSets' bind [] vsC $ S.toList vsP

applyBindingsToSets'
  :: MonadPlus mp
  => Binding -> VarList -> VarSet -> VarList -> mp (VarSet,VarSet)
\end{code}

Pattern list (set) empty, return the leftovers
\begin{code}
applyBindingsToSets' bind vlP' vsC [] = return (vsC,S.fromList vlP')
\end{code}

First pattern variable is standard:
\begin{code}
applyBindingsToSets' bind vlP' vsC (gP@(StdVar vP):vlP)
 = case lookupBind bind vP of
    Nothing -> applyBindingsToSets' bind (gP:vlP') vsC vlP
    Just (BindTerm _) -> fail "vsMatch: pattern var already bound to term."
    Just (BindVar vB)
     -> let gB = StdVar vB in
        if gB `S.member` vsC
        then applyBindingsToSets' bind vlP' (S.delete gB vsC) vlP
        else fail "vsMatch: std-pattern var's binding not in candidate set."
\end{code}

First pattern variable is a list-variable:
\begin{code}
applyBindingsToSets' bind vlP' vsC (gP@(LstVar lvP):vlP)
 = case lookupLstBind bind lvP of
    Nothing -> applyBindingsToSets' bind (gP:vlP') vsC vlP
    Just (BindSet vsB)
     -> if vsB `S.isSubsetOf` vsC
        then applyBindingsToSets' bind vlP' ((S.\\) vsC vsB) vlP
        else fail "vsMatch: pattern list-var's binding not in candidate set."
    _ -> fail "vsMatch: list-variable bound to variable-list.c"
\end{code}

\newpage
\subsubsection{Free Variable-Set Matching}

Here we are doing variable-set matching where all of the
pattern variables are free, \textit{i.e.}, not already in the binding.
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
\begin{code}
vsFreeMatch :: MonadPlus mp
              => [VarTable] -> Binding
              -> CBVS -> PBVS
              -> VarSet -> VarSet
              -> mp Binding
vsFreeMatch vts bind cbvs pbvs vsC vsP
  = let
      (uvsC,kvsC,ulsC,klsC) = vsClassify vts vsC
      (uvsP,kvsP,ulsP,klsP) = vsClassify vts vsP
      klsC' = klsC S.\\ klsP
      klsP' = klsP S.\\ klsC
    in if kvsP `S.isSubsetOf` kvsC
       then vsFreeMatch2 vts bind cbvs pbvs
               (uvsC,kvsC S.\\ kvsP,ulsC,klsC')
               (uvsP,ulsP) klsP'
       else fail "vsFreeMatch: known vars missing."
\end{code}

A quick std/list-variable classifier:
\begin{code}
vsClassify vts vs
  =  clsfy [] [] [] [] $ S.toList vs
  where
      clsfy uvs kvs uls kls []
        = (S.fromList uvs, S.fromList kvs, S.fromList uls, S.fromList kls)
      clsfy uvs kvs uls kls (StdVar v:gvs)
        = case lookupVarTables vts v of
            UnknownVar  ->  clsfy (v:uvs) kvs uls kls gvs
            _           ->  clsfy uvs (v:kvs) uls kls gvs
      clsfy uvs kvs uls kls (LstVar lv@(LVbl v _ _):gvs)
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

We work with
\begin{code}
-- klsC and klsP are disjoint
vsFreeMatch2 vts bind cbvs pbvs
  vsC@(uvsC,kvsC,ulsC,klsC)
  (uvsP,ulsP) klsP
  = error "vsFreeMatch2: NYI"
\end{code}

\newpage
\textbf{SOON TO BE DEPRECATED}
\begin{code}
vsFreeMatch' :: MonadPlus mp
              => [VarTable] -> Binding
              -> CBVS -> PBVS
              -> VarSet -> VarSet
              -> mp Binding
\end{code}

If one or both sets are empty then we can easily resolve matters,
\begin{code}
vsFreeMatch' vts bind cbvs pbvs vsC vsP
 | S.null vsP
    = if S.null vsC then return bind
      else fail $ unlines
        [ "vsFreeMatch: too many candidate variables."
        , "vsC = " ++ show vsC ]
 | S.null vsC
    = if S.null $ S.filter isStdV vsP
      then bindLVarSetToNull vts bind (S.toList vsP)
      else fail $ unlines
        [ "vsMatch: too many std. pattern variables."
        , "vsC = "  ++ show vsC
        , "vsP = "  ++ show vsP
        , "bind:"   ++ show bind
        ]
\end{code}

If both sets are non-empty,
we have potentially non-deterministic outcomes.
First we try to pattern-match the standard variables.
Then we will attempt the list-variable matching.
\begin{code}
 | otherwise
    = do (bind',svsC',lvsP') <- vsFreeStdMatch vts bind cbvs pbvs vsC vsP
         vsFreeLstMatch vts bind' cbvs pbvs svsC' lvsP'
\end{code}

Once more, we need to check for list-variables that are known,
and defined as non-null variable lists.
Note that a known-list variable can match null, if it has subtracted
identifiers, but that will then induce bindings from the subtracted
identifiers to the entirety of the corresponding known variable-list.
\begin{code}
bindLVarSetToNull vts bind [] = return bind
bindLVarSetToNull vts bind ((LstVar lv):vl)
 | canMatchNullSet vts lv  =  do bind' <- bindLVarToVSet lv S.empty bind
 -- Need to bind any 'less' ids to what's known (sub-match!)
                                 bindLVarSetToNull vts bind' vl
 | otherwise  =  fail "vsMatch: known list-var. cannot match null."
bindLVarSetToNull _ _ (_:_) = fail "bindLVarSetToNull: std. variables not allowed."
\end{code}

\begin{code}
canMatchNullSet :: [VarTable] -> ListVar -> Bool
canMatchNullSet vts lv
  = case lookupLVarTables vts (varOf lv) of
      KnownVarSet vs _ _  ->  S.null vs
      _                   ->  True
\end{code}

\newpage

\begin{code}
vsFreeStdMatch :: MonadPlus m
               => [VarTable] -> Binding -> CBVS -> PBVS
               -> Set GenVar -> Set GenVar
               -> m (Binding, Set GenVar, Set GenVar)
\end{code}

First, pairing up very standard pattern variable
with one standard candidate variable,
if possible.
First we break down both sets into variables of the four various
temporal classifications
(static${}_s$, dynamic(before${}_b$, during${}_d$, after${}_a$)),
and check their sizes.
Let $p_s$, $p_b$, $p_d$, and $p_a$ denote the
number of standard pattern variables of each class,
and $c_s$, $c_b$, $c_d$, and $c_a$ denote similarly
for the standard candidate variables.
Given that each standard pattern must bind
to exactly one distinct candidate variable,
we get the following size constraints that must be satisfied:
\begin{eqnarray*}
   p_b \leq c_b && e_b = c_b - p_b
\\ p_d \leq c_d && e_d = c_d - p_d
\\ p_a \leq c_a && e_a = c_a - p_a
\\ p_s &\leq& c_s + e_b + e_d + e_a
\end{eqnarray*}

We first split the standard variables of both pattern and candidate sets,
check the inequalities above,
and then proceed to match the dynamics sets first,
followed by the static matching.
Once the standard matching is done,
we proceed to look at the list-variable patterns.
\begin{code}
vsFreeStdMatch vts bind cbvs pbvs vsC vsP
  | eb < 0  =  fail "vsMatch: too few std. candidate Before variables."
  | ed < 0  =  fail "vsMatch: too few std. candidate During variables."
  | ed < 0  =  fail "vsMatch: too few std. candidate After variables."
  | S.size vsPs > S.size vsCs + eb + ed + ea
            =  fail "vsMatch: too many std. pattern Static variables."
  | otherwise
    =  do (bindb,vsCb') <- vsFreeStdMatch' vts bind  cbvs pbvs vsCb vsPb
          (bindd,vsCd') <- vsFreeStdMatch' vts bindb cbvs pbvs vsCd vsPd
          (binda,vsCa') <- vsFreeStdMatch' vts bindd cbvs pbvs vsCa vsPa
          -- Static matches anything
          let vsCs' = S.unions [vsCs,vsCb',vsCd',vsCa']
          (binds,svsC') <- vsFreeStdMatch' vts binda cbvs pbvs vsCs' vsPs
          return (binds,S.union lvsC svsC',lvsP)
  where
    (lvsC,svsC) = S.partition isLstV vsC
    (lvsP,svsP) = S.partition isLstV vsP
    (vsCs,vsCb,vsCd,vsCa) = whenPartition svsC
    (vsPs,vsPb,vsPd,vsPa) = whenPartition svsP
    eb = S.size vsCb - S.size vsPb
    ed = S.size vsCd - S.size vsPd
    ea = S.size vsCa - S.size vsPa
\end{code}


\newpage
Matching $m$ pattern variables against $n$ candidate variables
allows for $n!/(m-n)!$ possible outcomes.
\begin{code}
vsFreeStdMatch' ::
  MonadPlus m =>
  [VarTable] -> Binding -> CBVS -> PBVS
  -> Set GenVar -> Set GenVar
  -> m (Binding, Set GenVar)
\end{code}
We now do a number of matches,
based on a ``rotation'' of the set of pattern variables.
This should result in $m$ matches.
\begin{code}
-- all variables are standard, of the same temporality.
-- #vsC >= #vsP
vsFreeStdMatch' vts bind cbvs pbvs vsC vsP
 | psize == 0  =  return (bind,vsC)
 | psize == 1  =  do bind' <- zipVarVarBind bind vlC vlP
                     return (bind',S.fromList vlC')
 | otherwise  =   do bind' <- vsFreeStdMatch'' vts bind cbvs pbvs vlC vlP []
                     return (bind',S.fromList vlC')
 where
   psize = S.size vsP
   (vlC,vlC') = splitAt psize $ S.toList vsC ; vlP = S.toList vsP
\end{code}

\begin{code}
vsFreeStdMatch'' ::
  MonadPlus m =>
  [VarTable] -> Binding -> CBVS -> PBVS
  -> [GenVar] -> [GenVar] -> [GenVar]
  -> m Binding
-- #vlC = #vlP1 + #vlP2
vsFreeStdMatch'' vts bind cbvs pbvs vlC [] vlP2
 = zipVarVarBind bind vlC vlP2
vsFreeStdMatch'' vts bind cbvs pbvs vlC vlP1@(vP:vlP1') vlP2
 = zipVarVarBind bind vlC (reverse vlP2 ++ vlP1)
   `mplus`
   vsFreeStdMatch'' vts bind cbvs pbvs vlC vlP1' (vP:vlP2)
\end{code}

This code, and its local definitions, may belong somewhere else.
\begin{code}
whenPartition :: VarSet -> (VarSet,VarSet,VarSet,VarSet)
whenPartition vs = (vsStatic,vsBefore,vsDuring,vsAfter)
 where
  isStatic gv  =  timeGVar gv == Static
  isBefore gv  =  timeGVar gv == Before
  isAfter gv   =  timeGVar gv == After
  isDuring gv  =  case timeGVar gv of During _ -> True ; _ -> False
  (vsStatic,vs1)      =  S.partition isStatic vs
  (vsBefore,vs2)      =  S.partition isBefore vs1
  (vsDuring,vsAfter)  =  S.partition isDuring vs2
\end{code}

\begin{code}
zipVarVarBind :: Monad m => Binding -> [GenVar] -> [GenVar] -> m Binding
-- both lists should be  the same length
zipVarVarBind bind [] []  =  return bind
zipVarVarBind bind (gC:vlC) (gP:vlP)
 = do bind' <- bindGVarToGVar gP gC bind
      zipVarVarBind bind' vlC vlP
-- defensive programming
zipVarVarBind bind  _ []  =  error "zipVarVarBind: vlP too small"
zipVarVarBind bind []  _  =  error "zipVarVarBind: vlp too large"
\end{code}

\newpage

We have a collection of unbound pattern list-variables
that we want to match against the remaining candidate variables,
inlcuding all the list-variables,
plus any standard variables left by the previous standard matching phase.
\begin{code}
vsFreeLstMatch :: MonadPlus mp
               => [VarTable] -> Binding -> CBVS -> PBVS
               -> VarSet -> VarSet
               -> mp Binding
\end{code}

If our pattern is empty,
then we succeed if the candidate is also empty,
otherwise we fail.
\begin{code}
-- variable-set pattern lvsP contains only list-variables.
vsFreeLstMatch vts bind cbvs pbvs vsC lvsP
  | null lvsP = if null vsC then return bind
                else fail "vsFreeLstMatch: too many candidate variables."
\end{code}
If the candidate is empty then we succeed only if
all the remaining pattern variables can bind to the empty set.
\begin{code}
--vsFreeLstMatch vts bind cbvs pbvs vsC lvsP
  | null vsC = let lvs = listVarSetOf lvsP in
               if all (canMatchNullSet vts) lvs
               then bindLVarSetToNull vts bind $ S.toList lvsP
               else fail "vsMatch: known list pattern can't match null."
\end{code}
We extract a pattern list variable,
and handle it much in the same way as \texttt{vlFreeMatch} above.
Here we also try some non-deterministic matching, also with $N=2$.
\begin{code}
--vsFreeLstMatch vts bind cbvs pbvs vsC lvsP -- vsC, lvsP not null
  | otherwise
    = case lookupLVarTables vts (varOf lvP) of
       KnownVarSet vsK _ _
        -> do (bind',vsC') <- vsKnownMatch vts bind cbvs pbvs vsC vsK gvP
              vsFreeLstMatch vts bind' cbvs pbvs vsC' lvsP'
       KnownVarList vlK _ _
        -> do (bind',vsC')
                     <- vsKnownMatch vts bind cbvs pbvs vsC (S.fromList vlK) gvP
              vsFreeLstMatch vts bind' cbvs pbvs vsC' lvsP'
       _
        -> vsFreeMatchN vts bind cbvs pbvs vsC lvP lvsP' 0
           `mplus`
           vsFreeMatchN vts bind cbvs pbvs vsC lvP lvsP' 1
           `mplus`
           vsFreeMatchN vts bind cbvs pbvs vsC lvP lvsP' 2
  where (gvP@(LstVar lvP),lvsP') = (S.elemAt 0 lvsP, S.deleteAt 0 lvsP)
\end{code}

\newpage
Similarly to \texttt{vlKnownMatch} above, we may need to expand all known
variables in both \texttt{vsK} and \texttt{vsC}.

\begin{code}
vsKnownMatch :: MonadPlus mp
             => [VarTable] -> Binding -> CBVS -> PBVS
             -> VarSet -> VarSet -> GenVar
             -> mp ( Binding, VarSet )
-- not null vsC
vsKnownMatch vts bind cbvs pbvs vsC vsK gvP@(LstVar lvP) -- ListVar !
 | not $ S.null gvCs
    = do bind' <- bindLVarToVSet lvP gvCs bind
         return (bind',vsC `removeS` gvCs)
 | vsK `withinS` vsC
    = do bind' <- bindLVarToVSet lvP (vsC `intsctS` vsK) bind
         return (bind',vsC `removeS` vsK)
 | otherwise -- quick matches don't work, need to go to full expansions
    = do vsKx <- expandKnownSets vts vsK
         vsCx <- expandKnownSets vts vsC
         (vsC1,vsC2) <- vsKnownXMatch vts vsC vsCx vsKx
         bind' <- bindLVarToVSet lvP vsC1 bind
         return (bind',vsC2)
 where
   gvCs = vsC `intsctS` S.singleton gvP
   gvC  = S.elemAt 0 gvCs
\end{code}

We keep expanding variables known as sets of (other) variables.
\begin{code}
expandKnownSet :: Monad m => [VarTable] -> GenVar -> m VarSet

expandKnownSet vts gv@(StdVar v)
  = case lookupVarTables vts v of
      KnownConst (Var _ kc)  ->  expandKnownSet vts $ StdVar kc
      _                      ->  return $ S.singleton gv

expandKnownSet vts gv@(LstVar lv)
  = case lookupLVarTables vts (varOf lv) of
      KnownVarSet kvs _ _  ->  expandKnownSets vts kvs
      UnknownListVar   ->  return $ S.singleton gv
      _                ->  fail "expandKnownSet: found variable-lists!"

expandKnownSets :: Monad m => [VarTable] -> VarSet -> m VarSet
expandKnownSets vts vs
  = fmap S.unions $ sequence $ map (expandKnownSet vts) $ S.toList vs
\end{code}


\includegraphics[scale=0.5]{doc/images/matching-known-varsets}

Matching fully-expanded pattern variable-set against
partially-expanded candidate variable-set.
\begin{code}
vsKnownXMatch vts vsC vsCx vsKx
  | vsKx `withinS` vsCx
     = do vsCm <- getCorrCandidates vts [] vsKx $ S.toList vsC
          return (vsCm, vsC `removeS` vsCm)
  | otherwise
      = fail $ unlines
          [ "vsMatch: some pattern var-set is not in candidate."
          , "vsKx = " ++ show vsKx
          , "vsCx = " ++ show vsCx
          ]
\end{code}

Find the candidate variables in \texttt{vsC} that expand into
variables within \texttt{vsKx}.
\begin{code}
getCorrCandidates vts rvsC vsKx []
 | S.null vsKx  =  return $ S.fromList rvsC
 | otherwise    =   fail "vsMatch: not all pattern-set covered."
getCorrCandidates vts rvsC vsKx (gvC:vsC)
 = case expandKnownSet vts gvC of
    Nothing  ->  fail "vsMatch: expandKnownSet fails."
    Just gvCx
     | gvCx `withinS` vsKx
                  -> getCorrCandidates vts (gvC:rvsC) (vsKx `removeS` gvCx) vsC
     | otherwise  -> getCorrCandidates vts rvsC       vsKx             vsC
\end{code}

\newpage
We match \texttt{lvP} against upto \texttt{n} candidate variables.
\begin{code}
vsFreeMatchN vts bind cbvs pbvs vsC lvP lvsP n
 = do bind' <- bindLVarToVSet lvP firstnC bind
      vsFreeLstMatch vts bind' cbvs pbvs restC lvsP
 where
  (fv,rv) = splitAt n $ S.toList vsC
  firstnC = S.fromList fv
  restC = S.fromList rv
\end{code}

\newpage
\subsection{Substitution Matching}

Here $G$ denotes either one standard variable,
or a collection of general variables,
while $g$ denotes one general variable.
Similarly, $r$ denotes on one substutition replacement (list-variable or term)
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
sMatch :: MonadPlus mp
       => [VarTable] -> Binding -> CBVS -> PBVS
       -> Substn -> Substn
       -> mp Binding
\end{code}

We match substitutions by first ignoring the replacement terms,
and doing a variable-set match on the variables.
We then use the new bindings to identify the corresponding terms,
and check that they match.
\begin{code}
sMatch vts bind cbvs pbvs (Substn tsC lvsC) (Substn tsP lvsP)
 = do bind'  <- vsMatch      vts  bind  cbvs pbvs vsC vsP
      (bind'',tsC') <- tsMatchCheck vts  bind' cbvs pbvs tsC $ S.toList tsP
      if all (isVar . snd) tsC'
      then lvsMatchCheck vts bind'' cbvs pbvs (tsC' +++ lvsC) $ S.toList lvsP
      else fail $ unlines
             [ "sMatch: some leftover std-replacement is not a Var."
             , "tsP  = " ++ show tsP
             , "tsC  = " ++ show tsC
             , "tsC' = " ++ show tsC'
             ]
 where
  vsC = S.map (StdVar . fst) tsC `S.union` S.map (LstVar . fst) lvsC
  vsP = S.map (StdVar . fst) tsP `S.union` S.map (LstVar . fst) lvsP
  ts +++ lvs = (S.map liftVV ts `S.union` S.map liftLL lvs)
  liftVV (v,(Var _ u))  =  (StdVar v, StdVar u )
  liftLL (lv,lu      )  =  (LstVar lv,LstVar lu)
\end{code}

\newpage
All the variable/term matches.
$$ \beta \uplus \{\beta_{t_i}\} \vdash R_{C_j} :: r_{P_i} \leadsto \beta_{r_i} $$
where $R$ is a single term $t$, and $r$ is a standard variable $v$,
so giving
$$ \beta \uplus \{\beta_{t_i}\} \vdash t_{C_j} :: v_{P_i} \leadsto \beta_{r_i}. $$
For every $(v_P,t_P)$ we search for a $(v_C,t_C)$ where $\beta(v_P)=v_C$,
and then we attempt to match $t_C$ against $t_P$.
We need to return all pairs in the \texttt{TermSub} not found in this process.
\begin{code}
tsMatchCheck :: MonadPlus mp
             => [VarTable] -> Binding -> CBVS -> PBVS
             -> TermSub -> [(Variable,Term)]
             -> mp (Binding, TermSub)

tsMatchCheck vts bind cbvs pbvs tsC []  =  return (bind,tsC)
tsMatchCheck vts bind cbvs pbvs tsC ((vP,tP):tsP)
 = do (bind',tsC') <- vtMatchCheck vts bind cbvs pbvs tsC tP vP
      tsMatchCheck vts bind' cbvs pbvs tsC' tsP
\end{code}

Given a $(v_P,t_P)$, search for a $(v_C,t_C)$ where $\beta(v_P)=v_C$,
and attempt to match $t_C$ against $t_P$.
\begin{code}
vtMatchCheck :: MonadPlus mp
             => [VarTable] -> Binding -> CBVS -> PBVS
             -> TermSub -> Term -> Variable
             -> mp (Binding,TermSub)

vtMatchCheck vts bind cbvs pbvs tsC tP vP
 = case lookupBind bind vP of
     Nothing            ->  fail "vtMatchCheck: Nothing SHOULD NOT OCCUR!"
     Just (BindTerm _)  ->  fail "vtMatchCheck: BindTerm SHOULD NOT OCCUR!"
     Just (BindVar vB)
       -> let tsB = S.filter ((==vB).fst) tsC
          in if S.size tsB /= 1
              then fail "vtMatchCheck: #tsB /= 1 SHOULD NOT OCCUR!"
              else let tB = snd $ S.elemAt 0 tsB
                   in do bind' <- tMatch vts bind cbvs pbvs tB tP
                         return (bind', tsC S.\\ tsB)
\end{code}

\newpage
All the list-var/list-var matches, along with leftover standard vars.
$$ \beta \uplus \{\beta_{t_i}\} \vdash R_{C_j} :: r_{P_i} \leadsto \beta_{r_i} $$
where $R$ is a list or set of general variables term $gs$,
and $r$ is a list-variable $lv$,
so giving
$$ \beta \uplus \{\beta_{t_i}\} \vdash gs_{C_j} :: lv_{P_i} \leadsto \beta_{r_i}. $$
For every $(tlv_P,rlv_P)$ we search for all $(tlv_C,rlv_C)$
where $tlv_C \in \beta(tlv_P)$,
and attempt to bind $rlv_P$ to all the corresponding $rlv_C$.
\begin{code}
lvsMatchCheck :: MonadPlus mp
       => [VarTable] -> Binding -> CBVS -> PBVS
       -> Set (GenVar,GenVar) -> [(ListVar,ListVar)]
       -> mp Binding

lvsMatchCheck vts bind cbvs pbvs gvsC []  =  return bind
lvsMatchCheck vts bind cbvs pbvs gvsC ((tlvP,rlvP):lvsP)
 = do bind' <- lvlvMatchCheck vts bind cbvs pbvs gvsC rlvP tlvP
      lvsMatchCheck vts bind' cbvs pbvs gvsC lvsP
\end{code}

Given a $(tlv_P,rlv_P)$, search for all $(tlv_C,rlv_C)$
where $tlv_C \in \beta(tlv_P)$,
and then we attempt to bind $rlv_P$ to all the corresponding $rlv_C$.
\begin{code}
lvlvMatchCheck :: MonadPlus mp
               => [VarTable] -> Binding -> CBVS -> PBVS
               -> Set (GenVar,GenVar) -> ListVar -> ListVar
               -> mp Binding

lvlvMatchCheck vts bind cbvs pbvs gvsC rlvP tlvP
 = case lookupLstBind bind tlvP of
     Nothing            ->  fail "lvlvMatchCheck: Nothing SHOULD NOT OCCUR!"
     Just (BindList bvlC) ->
      let gvlB = S.toList $ S.filter ((inlist bvlC).fst) gvsC
      in bindLVarToVList rlvP (map snd gvlB) bind
     Just (BindSet bvsC) ->
      let gvsB = S.filter ((inset bvsC).fst) gvsC
      in bindLVarToVSet rlvP (S.map snd gvsB) bind
 where
   inlist vl gv  =  gv   `elem`   vl
   inset  vs gv  =  gv `S.member` vs
\end{code}


\newpage
\subsection{Sub-Typing}

No surprises here.
\begin{code}
isSubTypeOf :: Type -> Type -> Bool
_ `isSubTypeOf` ArbType  =  True
ArbType `isSubTypeOf` _  =  False
_ `isSubTypeOf` (TypeVar _)  =  True
(TypeApp i1 ts1) `isSubTypeOf` (TypeApp i2 ts2)
 | i1 == i2  =  ts1 `areSubTypesOf` ts2
(DataType i1 fs1) `isSubTypeOf` (DataType i2 fs2)
 | i1 == i2  =  fs1 `areSubFieldsOf` fs2
(FunType tf1 ta1) `isSubTypeOf` (FunType tf2 ta2) -- tf contravariant !
   = tf2 `isSubTypeOf` tf1 && ta1 `isSubTypeOf` ta2
(GivenType i1) `isSubTypeOf` (GivenType i2)  = i1 == i2
_ `isSubTypeOf` _ = False
\end{code}

\begin{code}
areSubTypesOf :: [Type] -> [Type] -> Bool
[]       `areSubTypesOf` []        =  True
(t1:ts1) `areSubTypesOf` (t2:ts2)  =  t1 `isSubTypeOf` t2 && ts1 `areSubTypesOf` ts2
_        `areSubTypesOf` _         =  False
\end{code}

\begin{code}
areSubFieldsOf :: [(Identifier,[Type])] -> [(Identifier,[Type])] -> Bool
[] `areSubFieldsOf` []  =  True
((i1,ts1):fs1) `areSubFieldsOf` ((i2,ts2):fs2)
 | i1 == i2             =  ts1 `areSubTypesOf` ts2 && fs1 `areSubFieldsOf` fs2
_ `areSubFieldsOf` _    =  False
\end{code}


\newpage
\subsection{Building Variables from Identifiers}

\begin{code}
vr :: VarClass -> VarWhen -> Identifier -> Variable
vr vc vw i = Vbl i vc vw

lvr :: VarClass -> VarWhen -> Identifier -> ListVar
lvr vc vw i = LVbl (vr vc vw i) [] []
\end{code}
