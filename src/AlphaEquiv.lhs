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
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isJust)
-- import Control.Monad
-- import Data.List

-- import Utilities
-- import Control
import LexBase
import Variables
import AST
-- import FreeVars
-- import VarData
-- import Binding
-- import Matching


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

We check $\alpha$-equivalence by matching one term against the other,
tracking bound variables on both sides.
We expect everything to be equal,
except bound variables.
A bound variable can match a different bound variable,
provided that the only difference is the variable identifier.
We record a binding between the corresponding general variables,
that must be one-to-one.
We use a helper function that tracks bound variables from each side
along with a bijection between them.
\begin{code}
isAlphaEquivalent t1 t2 = isJust $ isAEquiv S.empty S.empty M.empty t1 t2
\end{code}

We maintain the bound variables and the bijection at the general variable level.
\begin{code}
isAEquiv :: Monad m => VarSet -> VarSet -> (Map GenVar GenVar) -> Term -> Term
         ->    m (Map GenVar GenVar)
\end{code}

Values must be equal:
\begin{code}
isAEquiv _ _ bij (Val tk1 k1) (Val tk2 k2)
  | tk1 == tk2 && k1 == k2  =  return bij
\end{code}

Both variables must have same free/bound state;
Bound variables must form a bijective map;
Free variables must be equal;
\begin{code}
isAEquiv bvs1 bvs2 bij (Var tk1 v1) (Var tk2 v2)
  | tk1 /= tk2  =  fail "not a-equiv"
  | isBnd1 /= isBnd2  =  fail "not a-equiv"
  | isBnd1  =  checkAlphaBijection bij gv1 gv2
  | v1 == v2  =  return bij
  where
    (gv1,gv2) = (StdVar v1,StdVar v2)
    isBnd1 = gv1 `S.member` bvs1
    isBnd2 = gv2 `S.member` bvs2
\end{code}

Constructors must have the same number of sub-terms,
with the corresponding ones being equivalent.
\begin{code}
isAEquiv bvs1 bvs2 bij (Cons tk1 sb1 n1 ts1) (Cons tk2 sb2 n2 ts2)
  | tk1 /= tk2  =  fail "not a-equiv"
  | sb1 /= sb2  =  fail "not a-equiv"
  | n1  /= n2   =  fail "not a-equiv"
  | otherwise   =  areAlphas bvs1 bvs2 bij ts1 ts2
\end{code}

We need to add the \texttt{vs}$i$ to the \texttt{bvs}$i$,
while also removing them from \texttt{bij};
Changes to \texttt{bij} due to free variables in \texttt{tm}$i$
need to be kept.
TBD
\begin{code}
isAEquiv bvs1 bvs2 bij (Bnd tk1 n1 vs1 tm1) (Bnd tk2 n2 vs2 tm2)
  | tk1 /= tk2  =  fail "not a-equiv"
  | n1  /= n2   =  fail "not a-equiv"
\end{code}

TBD
\begin{code}
isAEquiv bvs1 bvs2 bij (Lam tk1 n1 vl1 tm1) (Lam tk2 n2 vl2 tm2)
  | tk1 /= tk2  =  fail "not a-equiv"
  | n1  /= n2   =  fail "not a-equiv"
\end{code}

TBD
\begin{code}
isAEquiv bvs1 bvs2 bij (Cls n1 tm1) (Cls n2 tm2)
  | n1 /= n2  =  fail "not a-equiv"
\end{code}

TBD
\begin{code}
isAEquiv bvs1 bvs2 bij (Sub tk1 tm1 s1) (Sub tk2 tm2 s2)
  | tk1 /= tk2  =  fail "not a-equiv"
\end{code}

For now, we consider the list-variables as free at this point.
\begin{code}
isAEquiv bvs1 bvs2 bij (Iter tk1 sa1 na1 si1 ni1 lvs1)
                       (Iter tk2 sa2 na2 si2 ni2 lvs2)
  | tk1 /= tk2  =  fail "not a-equiv"
  | sa1 /= sa2  =  fail "not a-equiv"
  | na1 /= na2  =  fail "not a-equiv"
  | si1 /= si2  =  fail "not a-equiv"
  | ni1 /= ni2  =  fail "not a-equiv"
  | otherwise   =  checkAlphaBijections bij gvs1 gvs2
  where (gvs1,gvs2) = (map LstVar lvs1, map LstVar lvs2)
\end{code}

Types must be equal:
\begin{code}
isAEquiv bvs1 bvs2 bij (Typ typ1) (Typ typ2)
  | typ1 == typ2  =  return bij
\end{code}

Everything else is a fail.
\begin{code}
isAEquiv _ _ _ _ _ = fail "not a-equiv"
\end{code}

Given a bijection, and two (bound) general variables,
see if they are already noted, and add if not.
Fail if they are mismatched.
\begin{code}
checkAlphaBijection :: Monad m => (Map GenVar GenVar) -> GenVar -> GenVar
                    -> m (Map GenVar GenVar)

checkAlphaBijection bij gv1 gv2
  = if gv1 `M.member` bij
      then
        case M.lookup gv1 bij of
          Just gv2' | gv2 == gv2'  ->  return bij
                    | otherwise  ->  fail "not a-equiv"
          Nothing -> if gv2 `elem` M.elems bij
                       then fail "not a-equiv"
                       else return (M.insert gv1 gv2 bij)
      else -- not(gv1 `M.member` bij)
        if gv2 `elem` M.elems bij
          then fail "not a-equiv"
          else return (M.insert gv1 gv2 bij)

checkAlphaBijections :: Monad m => (Map GenVar GenVar) -> [GenVar] -> [GenVar]
                     -> m (Map GenVar GenVar)

checkAlphaBijections bij [] [] = return bij
checkAlphaBijections bij (gv1:gvs1) (gv2:gvs2)
  = do bij' <- checkAlphaBijection bij gv1 gv2
       checkAlphaBijections bij' gvs1 gvs2
checkAlphaBijections _ _ _ = fail "not a-equiv"
\end{code}

Doing it with term lists:
\begin{code}
areAlphas :: Monad m => VarSet -> VarSet -> (Map GenVar GenVar)
          -> [Term] -> [Term]
          -> m (Map GenVar GenVar)

areAlphas bvs1 bvs2 bij [] [] = return bij
areAlphas bvs1 bvs2 bij (t1:ts1) (t2:ts2)
 = do bij' <- isAEquiv bvs1 bvs2 bij t1 t2
      areAlphas bvs1 bvs2 bij' ts1 ts2
areAlphas _ _ _ _ _ = fail "not a-equiv"
\end{code}
