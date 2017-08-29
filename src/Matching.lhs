\section{Matching}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Matching ( match
                ) where
--import Data.Maybe (fromJust)
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
tMatch vts bind _ _ kC@(Val _ _) kP@(Val _ _)
 | kC == kP  =  return bind
\end{code}

\begin{verbatim}
Cons tk n ts
Var tk v
Bind tk n vl tm
Lam tk n vs tm
Sub tk tm s
Iter tk na ni lvs
\end{verbatim}

Any other case results in failure:
\begin{code}
tMatch _ _ _ _ _ _ = fail "tMatch: structural mismatch."
\end{code}
