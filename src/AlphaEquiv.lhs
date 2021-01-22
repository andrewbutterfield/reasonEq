\section{$\alpha$ Equivalence}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2021

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AlphaEquiv
( isAlphaEquivalent
, (=~=)
  -- below exported for testing
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
import AST
import FreeVars
import VarData
import Binding
import Matching


import Debug.Trace
dbg msg x = trace (msg ++ show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\subsection{Introduction}

We say that two terms are $\alpha$-equivalent,
where there exists a bijective mapping between their bound variables,
that when applied to one, makes it syntactically equal to the other.

Our proof engine compares the current state of a proof goal with
a target predicate.
We could use full syntactic equality for this,
but then we would have to support proof steps that could help find
and apply the necessary bijection.

An example is the following:
\begin{verbatim}
(∃ O$_3 • (∃ O$_4 • P[O$_4/O$']∧(Q[O$_4,O$_3/O$,O$']∧R[O$_3/O$])))
(∃ O$_1 • (∃ O$_2 • P[O$_1/O$']∧(Q[O$_1,O$_2/O$,O$']∧R[O$_2/O$])))
\end{verbatim}
\begin{eqnarray*}
   \exists O_3 \bullet \exists O_4 \bullet
     P[O_4/O'] \land
     Q[O_4,O_3/O,O'] \land
     R[O_3/O]
\\ \exists O_1 \bullet \exists O_2 \bullet
  P[O_1/O'] \land
  Q[O_1,O_2/O,O'] \land
  R[O_2/O]
\end{eqnarray*}
Equivalence is shown here by proposing a bijective mapping of the form:
$$
 \setof{O_1 \mapsto O_4, O_2 \mapsto O_3}
$$
This mapping will result from a successful attempt to match the first
predicate above against the second.
This makes it simple to implement a check for $\alpha$-equivalence.

\begin{code}
isAlphaEquivalent :: Term -> Term -> Bool
(=~=)  =  isAlphaEquivalent
\end{code}


\begin{code}
isAlphaEquivalent  =  (==)  -- temporary placeholder
\end{code}
