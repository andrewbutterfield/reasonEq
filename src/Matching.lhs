\section{Matching}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Matching ( VarBindRange
                , pattern BindVar, pattern BindTerm
                , Binding
                , emptyBinding
                , bindVarToVar
                , bindVarToTerm
                , lookupBind
                ) where
--import Data.Maybe (fromJust)
import qualified Data.Map as M

--import Utilities
import LexBase
import AST
import VarData
\end{code}

\subsection{Matching Principles}

We want to match a candidate term ($T$) against a pattern term ($P$)
in some context ($\Gamma$),
to obtain a binding ($\beta$), if successful,
of pattern variables to appropriate term components.
$$
\Gamma \vdash T :: P  \leadsto \beta
$$
The context has two components,
the first ($\kappa$) being the known variables,
and the second ($B$) keeping track of bound variables.
We need to track bound variables for both
the candidate ($B_C$)
and pattern ($B_P$)
$$
\kappa;(B_T,B_P) \vdash T :: P  \leadsto \beta
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

We are not normally interested in the reason why a match fails,
so will generally use the \texttt{Maybe} type constructor.
However we code for a general monad with meaningful \texttt{fail} messages
to make it easier to debug or test.

\subsection{Bindings}

\subsubsection{Binding Types}

We have two parts to a binding,
one for variables, the other for list-variables.
The first part maps a variable to either a variable or a term
of the appropriate form.
\begin{code}
data VarBindRange
  = BV Variable
  | BT Term
  deriving (Eq, Ord, Show, Read)

pattern BindVar v <- BV v
pattern BindTerm t <- BT t

type VarBind = M.Map Variable VarBindRange
\end{code}

The other part maps a list variable to a list of variables.
\begin{code}
type ListVarBind = M.Map ListVar VarList
\end{code}

We put these together:
\begin{code}
newtype Binding = BD (VarBind, ListVarBind) deriving (Show, Read)

emptyBinding :: Binding
emptyBinding = BD (M.empty, M.empty)
\end{code}

\subsubsection{Binding Lookup}

Binding lookup is very straightforward,
with the minor wrinkle that we want to do it
in a general monadic setting.
\begin{code}
lookupBind :: Monad m => Binding -> Variable -> m VarBindRange
lookupBind (BD (vbinds,_)) v
  = case M.lookup v vbinds of
      Nothing   ->  fail ("lookupBind: Variable "++show v++" not found.")
      Just vbr  ->  return vbr

lookupLstBind :: Monad m => Binding -> ListVar -> m VarList
lookupLstBind (BD (_,lbinds)) lv
  = case M.lookup lv lbinds of
      Nothing    ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
      Just vlst  ->  return vlst
\end{code}

\subsubsection{Binding Insertion}

Insertion is more complicated,
as we have to ensure that the variable classification
matches the kind of thing to which it is being bound.
Observation pattern variables can match variables and expressions,
while expression and predicate pattern variables can only
match expressions and predicates respectively.

We have a design choice here: if we call the insertion function with
an innappropriate variable/thing mix, do we simply return the binding
unaltered, or do we fail?
We shall adopt the principle of failing in a general monadic setting,
noting however that the matching code we develop
should never fail in this way.

\paragraph{Binding Variable to Variable}~
\begin{code}
bindVarToVar :: Monad m => Variable -> Variable -> Binding -> m Binding
bindVarToVar pv cv bind = fail "bindVarToVar N.Y.I"
\end{code}

\paragraph{Binding Variable to Term}~
\begin{code}
bindVarToTerm :: Monad m => Variable -> Term -> Binding -> m Binding
bindVarToTerm pv ct bind = fail "bindVarToTerm N.Y.I"
\end{code}
