\section{Matching}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Matching ( match
                ) where
import Data.Maybe (isJust,fromJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad

--import Utilities
import LexBase
import AST
import VarData
import Binding
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
so we would like to return a list of bindings.
$$
\kappa;\beta;(B_C,B_P) \vdash C :: P \leadsto \beta s
$$
This leads us to adopt the \texttt{MonadPlus} class.

\newpage
\subsection{Matching Types}

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
match vts c p = tMatch vts emptyBinding noBVS noBVS c p
\end{code}

\subsection{Term Matching}

Term-matching is defined inductively over the pattern type.
\begin{code}
tMatch :: MonadPlus mp
       => [VarTable] -> Binding -> CBVS -> PBVS
       -> Candidate -> Pattern -> mp Binding
\end{code}
We start with the simple value and structural composite matches,
and then proceed to look at variable, binder and substitution patterns.

\subsubsection{Value Term-Pattern (\texttt{Val})}
Values only match themselves.
$$
\inferrule
   {k_C = k_P}
   {\kappa s;\beta;(B_C,B_P) \vdash k_C :: k_P \leadsto \beta}
   \quad
   \texttt{tMatch Val}
$$
\begin{code}
tMatch _ bind _ _ kC@(Val _ _) kP@(Val _ _)
 | kC == kP  =  return bind
\end{code}

\subsubsection{Constructor Term-Pattern (\texttt{Cons})}
Constructors match if they have the same name and kind
and the term-lists are of the same length and corresponding terms match.
$$
\inferrule
   { n_C = n_P
     \and
     \kappa s;\beta;(B_C,B_P) \vdash t_{C_i} :: t_{P_i} \leadsto \beta_i
     \and
     \beta' = \uplus\{\beta_i\}
   }
   {\kappa s;\beta;(B_C,B_P) \vdash C~n_C~ts_C :: C~n_P~ts_P \leadsto \beta'}
   \quad
   \texttt{tMatch Cons}
$$
Here $ts_X = \langle t_{X_1}, t_{X_2}, \dots t_{X_n} \rangle$.
\begin{code}
tMatch vts bind cbvs pbvs (Cons tkC nC tsC) (Cons tkP nP tsP)
 | tkC == tkP && nC == nP  =  tsMatch vts bind cbvs pbvs tsC tsP
\end{code}

\subsubsection{Variable Term-Pattern (\texttt{Var})}
Variable matching is complicated, so we farm it out,
as long as \texttt{TermKind}s match.
$$
\inferrule
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: v_P \leadsto \beta'}
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: V~v_P \leadsto \beta'}
   \quad
   \texttt{tMatch Var}
$$
\begin{code}
tMatch vts bind cbvs pbvs tC (Var tkP vP)
  | tkP == termkind tC  =  vMatch vts bind cbvs pbvs tC vP
\end{code}

Remaining Term Variants:
\begin{verbatim}
Bind tk n vl tm
Lam tk n vs tm
Sub tk tm s
Iter tk na ni lvs
\end{verbatim}

Any other case results in failure:
\begin{code}
tMatch _ _ _ _ _ _  =  fail "tMatch: structural mismatch."
\end{code}

\subsection{Term-List Matching}

For now a simple zip-like walk along both lists
(no precomputing length to abort early).
\begin{code}
tsMatch :: MonadPlus mp
        => [VarTable] -> Binding -> CBVS -> PBVS
        -> [Candidate] -> [Pattern] -> mp Binding
tsMatch _ bind _ _ [] [] = return bind
tsMatch vts bind cbvs pvbs (tC:tsC) (tP:tsP)
 = do bind1 <- tMatch vts bind cbvs pvbs tC tP
      tsMatch vts bind1 cbvs pvbs tsC tsP
tsMatch _ _ _ _ _ _  =  fail "tsMatch: structural mismatch."
\end{code}

\subsection{Variable Matching}

We assume here that candidate term and pattern variable
had the same \texttt{TermKind}.
\begin{code}
vMatch :: MonadPlus mp
       => [VarTable] -> Binding -> CBVS -> PBVS
       -> Candidate -> Variable -> mp Binding
\end{code}
We do a case split on the status of the pattern variable:
bound, known, or arbitrary.
\begin{code}
vMatch vts bind cbvs pvbs tC vP
 | StdVar vP `S.member` pvbs  =  bvMatch vts bind cbvs tC vP
 | isJust vPres               =  kvMatch vts bind tC (fromJust vPres) vP
\end{code}
\subsubsection{Arbitrary Pattern Variable}
$$
\inferrule
   { v_P \notin B_P \cup \mathbf{dom}\,\kappa s
     \and
     \beta' = \beta \uplus \{ v_P \mapsto t_C \}
   }
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: v_P \leadsto \beta'}
   \quad
   \texttt{vMatch Arbitrary}
$$
\begin{code}
 | otherwise                  =  bindVarToTerm vP tC bind
 where
   vPres = lookupBind bind vP
\end{code}

\subsubsection{Bound Pattern Variable}
$$
\inferrule
   { v_P \in B_P
     \and
     t_C = v_C
     \and
     v_C \in B_C
     \and
     \beta' = \beta \uplus \{ v_P \mapsto v_C \}
   }
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: v_P \leadsto \beta'}
   \quad
   \texttt{vMatch Bound-Var}
$$
\begin{code}
bvMatch vts bind cbvs tC vP = fail "bvMatch N.Y.I."
\end{code}

\subsubsection{Known Pattern Variable}
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C = v_C
     \and
     v_P = v_C
     \\\\
     \beta' = \beta \uplus \{ v_P \mapsto v_P \}
  }
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: v_P \leadsto \beta'}
   \quad
   \texttt{vMatch Known-Var-Refl}
$$
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C = v_C
     \and
     v_C = \kappa s(v_P)
     \\\\
     \beta' = \beta \uplus \{ v_P \mapsto v_C \}
  }
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: v_P \leadsto \beta'}
   \quad
   \texttt{vMatch Known-Var-Var}
$$
$$
\inferrule
   { v_P \notin B_P
     \and
     v_P \in \mathbf{dom}\,\kappa s
     \and
     t_C \neq v_c
     \and
     t_C = \kappa s(v_P)
     \\\\
     \beta' = \beta \uplus \{ v_P \mapsto t_C \}
  }
   {\kappa s;\beta;(B_C,B_P) \vdash t_C :: v_P \leadsto \beta'}
   \quad
   \texttt{vMatch Known-Var-Term}
$$
\begin{code}
kvMatch vts bind tC whatP vP = fail "kvMatch N.Y.I."
\end{code}
