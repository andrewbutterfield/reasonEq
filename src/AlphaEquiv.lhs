\section{$\alpha$ Equivalence}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2021-22

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AlphaEquiv
( isAlphaEquivalent
, (=~=)
  -- below exported for testing
, isAEquiv
, tryAlphaEquivalence
) where
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isJust)
-- import Control.Monad
-- import Data.List

import Utilities
-- import Control
import LexBase
import Variables
import AST
import FreeVars
-- import VarData
-- import Binding
-- import Matching


import Debug.Trace
dbg msg x = trace (msg ++ show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\newpage

\subsection{Introduction}

We say that two terms $t_1$ and $t_2$ are $\alpha$-equivalent
($t_1 \aeqv t_2$),
where there exists a bijective mapping between their bound variables,
that when applied to one, makes it syntactically equal to the other.

Our proof engine compares the current state of a proof goal with
a target predicate.
We could use full syntactic equality for this,
but then we would have to support proof steps that could help find
and apply the necessary bijection.

An example is the following:
\begin{eqnarray*}
  && \exists O_4 \bullet \exists O_3 \bullet
     P[O_4/O'] \land
     Q[O_4,O_3/O,O'] \land
     R[O_3/O]
\\&&\aeqv
\\&& \exists O_1 \bullet \exists O_2 \bullet
  P[O_1/O'] \land
  Q[O_1,O_2/O,O'] \land
  R[O_2/O]
\end{eqnarray*}
or the following:
\begin{eqnarray*}
  && \exists O_3,O_4 \bullet
     P[O_4/O'] \land
     Q[O_4,O_3/O,O'] \land
     R[O_3/O]
\\ && \aeqv
\\&& \exists O_1,O_2 \bullet
  P[O_1/O'] \land
  Q[O_1,O_2/O,O'] \land
  R[O_2/O]
\end{eqnarray*}Equivalence is shown here in each case 
by proposing a bijective mapping of the form:
$$
 \setof{P \mapsto P, Q \mapsto Q, R \mapsto R, O_1 \mapsto O_4, O_2 \mapsto O_3}
$$
This mapping will result from a successful attempt to match the first
predicate above against the second.
This makes it simple to implement a check for $\alpha$-equivalence.
We define a context that identifies bound variables on each side ($B_1$,$B_2$),
as well as a variable-variable bijective mapping $\beta$,
which leads to the following sequent:
$$
  B_1,B_2,\beta  \vdash  t_1 \aeqv t_2 \mapsto \beta'
$$
This describes a situation in which $\beta'$ is the desired bijection
that shows that $t_1$ and $t_2$ are $\alpha$-equivalent,
in a context where $B_1$ and $B_2$ are bound variables,
and $\beta$ is a bijection found from previous contexts.

So, at the top-level (no/empty context), $t_1$ is $\alpha$-equivalent to $t_2$ 
if we can derive 
$\emptyset,\emptyset,\epsilon \vdash t_1 \aeqv t_2 \mapsto \beta'$.
\begin{code}
isAlphaEquivalent :: Term -> Term -> Bool
isAlphaEquivalent t1 t2 = isJust $ isAEquiv S.empty S.empty M.empty t1 t2
\end{code}
We also introduce an infix operator $\equiv_\alpha$ for $\alpha$-equivalence.
\begin{code}
(=~=)  =  isAlphaEquivalent
\end{code}


\newpage

\subsection{Term $\alpha$-Equivalence}

$$
  B_1,B_2,\beta  \vdash  t_1 \aeqv t_2 \mapsto \beta'
$$
The function below returns $\beta'$ if successful.

We maintain the bound variables and the bijection at the general variable level.
\begin{code}
isAEquiv :: MonadFail m 
         => VarSet -> VarSet -> (Map GenVar GenVar) -> Term -> Term
         ->    m (Map GenVar GenVar)
\end{code}

\subsubsection{Value $\alpha$-equivalence}

Values must be equal:
$$
\inferrule%
  {k_1 = k_2}
  {\_,\_,\beta \vdash k_1 \equiv_\alpha k_2 \mapsto \beta}
$$
\begin{code}
isAEquiv _ _ bij (Val tk1 k1) (Val tk2 k2)
  | tk1 == tk2 && k1 == k2  =  return bij
  | otherwise  =  afail "literal values differ"
\end{code}

\subsubsection{Variable $\alpha$-equivalence}

Both variables must have same free/bound state;
Bound variables must be compatible and form a bijective map;
Free variables must be equal:
$$
  B_1,B_2,\beta  \vdash  v_1 \aeqv v_2
$$
\begin{code}
isAEquiv bvs1 bvs2 bij (Var tk1 v1) (Var tk2 v2)
  | tk1 /= tk2  =  afail "var kind differs"
  | otherwise   =  isAEquivVar bvs1 bvs2 bij v1 v2
\end{code}

\subsubsection{Constructor $\alpha$-equivalence}

Constructors must have the same number of sub-terms,
with the corresponding ones being equivalent:
$$
\inferrule%
  {k=\ell \and n_1=n_2 \and B_1,B_2,\beta_i  \vdash  s_i \aeqv t_i}
  { B_1,B_2,\beta\pluseq\beta_i  
    \vdash  
    n_1(s_1,\dots,s_k) \aeqv n_2(t_1,\dots,t_\ell) }
$$
\begin{code}
isAEquiv bvs1 bvs2 bij (Cons tk1 sb1 n1 ts1) (Cons tk2 sb2 n2 ts2)
  | tk1 /= tk2  =  afail "cons kind differs"
  | sb1 /= sb2  =  afail "cons subable differs"
  | n1  /= n2   =  afail "cons name differs"
  | otherwise   =  listAEquiv isAEquiv bvs1 bvs2 bij ts1 ts2
\end{code}

\subsubsection{Binder $\alpha$-equivalence}

We need to add the \texttt{vs}$i$ to the \texttt{bvs}$i$,
while also removing them from \texttt{bij};
Changes to \texttt{bij} due to free variables in \texttt{tm}$i$
need to be kept.
\begin{code}
isAEquiv bvs1 bvs2 bij (Bnd tk1 n1 vs1 tm1) (Bnd tk2 n2 vs2 tm2)
  | tk1        /= tk2         =  afail "bind kind differs"
  | n1         /= n2          =  afail "bind name differs"
  | S.size vs1 /= S.size vs2  =  afail "bind size differs"
  | otherwise =
      do bij'' <- isAEquiv bvs1' bvs2' bij' tm1 tm2
         let bijfree = M.filterWithKey (\k _ -> not(k `S.member` bvs1')) bij''
         return (bijfree `M.union` bij)
  where
    bvs1' = bvs1 `S.union` vs1
    bvs2' = bvs2 `S.union` vs2
    bij' = M.filterWithKey (\k _ -> not(k `S.member` vs1)) bij
\end{code}

\subsubsection{Lambda $\alpha$-equivalence}

Similar to above,
except that we can use the fact that we have bound variable lists,
rather than sets, to extend the bijective map before recursing over the terms.
\begin{code}
isAEquiv bvs1 bvs2 bij (Lam tk1 n1 vl1 tm1) (Lam tk2 n2 vl2 tm2)
  | tk1        /= tk2         =  afail "lambda kind differs"
  | n1         /= n2          =  afail "lambda name differs"
  | length vl1 /= length vl2  =  afail "lambda arity differs"
  | otherwise =
      do bij'' <- checkAlphaBijections bij' vl1 vl2
         bij''' <- isAEquiv bvs1' bvs2' bij'' tm1 tm2
         let bijfree = M.filterWithKey (\k _ -> not(k `S.member` bvs1')) bij'''
         return (bijfree `M.union` bij)
  where
    vs1 = S.fromList vl1
    vs2 = S.fromList vl2
    bvs1' = bvs1 `S.union` vs1
    bvs2' = bvs2 `S.union` vs2
    bij' = M.filterWithKey (\k _ -> not(k `S.member` vs1)) bij
\end{code}

\subsubsection{Closure $\alpha$-equivalence}

Closure is like bind, but where the \texttt{vs}$i$ cover all the
free-variables in the term.
We start body term analysis with an empty bijection,
and there are no free variables with changes that need to be returned.
\begin{code}
isAEquiv bvs1 bvs2 bij (Cls n1 tm1) (Cls n2 tm2)
  | n1 /= n2  =  afail "closure name differs"
  | otherwise =
      do bij' <- isAEquiv bvs1' bvs2' M.empty tm1 tm2
         return (seq bij' bij) -- force bij' evaluation
  where
    vs1 = theFreeVars $ freeVars tm1
    vs2 = theFreeVars $ freeVars tm2
    bvs1' = bvs1 `S.union` vs1
    bvs2' = bvs2 `S.union` vs2
\end{code}

\subsubsection{Substitution $\alpha$-equivalence}

For substitution, first check the terms, then the substitution lists.
\begin{code}
isAEquiv bvs1 bvs2 bij (Sub tk1 tm1 s1) (Sub tk2 tm2 s2)
  | tk1 /= tk2  =  afail "substn kind differs"
  | otherwise =
      do bij' <- isAEquiv bvs1 bvs2 bij tm1 tm2
         isAEquivSub bvs1 bvs2 bij' s1 s2
\end{code}

\subsubsection{Iteration $\alpha$-equivalence}

For now, we consider the list-variables as free at this point.
\begin{code}
isAEquiv bvs1 bvs2 bij (Iter tk1 sa1 na1 si1 ni1 lvs1)
                       (Iter tk2 sa2 na2 si2 ni2 lvs2)
  | tk1 /= tk2  =  afail "iteration kind differs"
  | sa1 /= sa2  =  afail "iteration outer subable differs"
  | na1 /= na2  =  afail "iteration outer name differs"
  | si1 /= si2  =  afail "iteration inner subable differs"
  | ni1 /= ni2  =  afail "iteration inner name differs"
  | otherwise   =  checkAlphaBijections bij gvs1 gvs2
  where (gvs1,gvs2) = (map LstVar lvs1, map LstVar lvs2)
\end{code}

\subsubsection{Type $\alpha$-equivalence}

Types must be equal:
\begin{code}
isAEquiv bvs1 bvs2 bij (Typ typ1) (Typ typ2)
  | typ1 == typ2  =  return bij
\end{code}

Everything else is a fail.
\begin{code}
isAEquiv _ _ _ _ _ = afail "term variants differ"
\end{code}

\newpage 

\subsection{Bound Variable $\alpha$-equivalence}

Are two variables equivalent?
\begin{code}
isAEquivVar bvs1 bvs2 bij v1 v2
  | isBnd1 /= isBnd2                      =  afails ("free vs. bound":dump)
  | isBnd1 && areAlphaCompatible gv1 gv2  =  checkAlphaBijection bij gv1 gv2
  | v1 == v2                              =  return $ M.insert gv1 gv2 bij
  | otherwise =  afails ("free var names differ":dump)
  where
    (gv1,gv2) = (StdVar v1,StdVar v2)
    isBnd1 = gv1 `S.member` bvs1
    isBnd2 = gv2 `S.member` bvs2
    dump  = [ "v1   = " ++ show v1
            , "v2   = " ++ show v2
            , "bvs1 = " ++ show bvs1
            , "bvs2 = " ++ show bvs2
            , "bij  = " ++ show bij
            ]
\end{code}

Are two list-variables equivalent?
\begin{code}
isAEquivLVar bvs1 bvs2 bij (LVbl v1 is1 js1) (LVbl v2 is2 js2)
  | is1 /= is2  =  afails ("lvar IS differ":dump)
  | js1 /= js2  =  afails ("lvar JS differ":dump)
  | otherwise = isAEquivVar bvs1 bvs2 bij v1 v2
  where
    dump  = [ "lv1   = " ++ show v1 ++ " " ++ show is1 ++ " " ++ show js1
            , "lv2   = " ++ show v2 ++ " " ++ show is2 ++ " " ++ show js2
            , "bvs1 = " ++ show bvs1
            , "bvs2 = " ++ show bvs2
            , "bij  = " ++ show bij
            ]
\end{code}

Given a bijection, and two (bound) general variables,
see if they are already noted, and add if not.
Fail if they are mismatched.
\begin{code}
checkAlphaBijection :: MonadFail m => (Map GenVar GenVar) -> GenVar -> GenVar
                    -> m (Map GenVar GenVar)

checkAlphaBijection bij gv1 gv2
  | areAlphaCompatible gv1 gv2
      = if gv1 `M.member` bij
          then
            case M.lookup gv1 bij of
              Just gv2' | gv2 == gv2'  ->  return bij
                        | otherwise    ->  afail "gen-var not bijective (1)"
              Nothing -> if gv2 `elem` M.elems bij
                           then afail "gen-var not bijective (2)"
                           else return (M.insert gv1 gv2 bij)
          else -- not(gv1 `M.member` bij)
            if gv2 `elem` M.elems bij
              then afail "gen-var not bijective (3)"
              else return (M.insert gv1 gv2 bij)
  | otherwise  =  afail "gen-var not bijective (4)"
\end{code}

A bound variable can match a different bound variable,
provided that the only difference is the variable identifier
or a \texttt{During} subscript.
\begin{code}
areAlphaCompatible (StdVar (Vbl _ class1 when1))
                   (StdVar (Vbl _ class2 when2))
  =  class1 == class2  &&  areCompatibleWhen when1 when2
areAlphaCompatible (LstVar (LVbl (Vbl _ class1 when1) is1 js1) )
                   (LstVar (LVbl (Vbl _ class2 when2) is2 js2) )
  =  class1 == class2  &&  areCompatibleWhen when1 when2
     && is1 == is2 && js1 == js2
areAlphaCompatible _ _ = False

areCompatibleWhen (During _) (During _)  =  True
areCompatibleWhen when1      when2       =  when1 == when2
\end{code}


With substitution we check the two sub-component pair-lists.
\begin{code}
isAEquivSub bvs1 bvs2 bij (Substn ts1 lvs1) (Substn ts2 lvs2)
  = do bij' <- isAEquivTermSub bvs1 bvs2 bij ts1 ts2
       isAEquivLVarSub bvs1 bvs2 bij' lvs1 lvs2
\end{code}

Terms replacing variables:
\begin{code}
isAEquivTermSub bvs1 bvs2 bij ts1 ts2
  | length tsl1 /= length tsl2 =  afail "term sublist lengths differ"
  | otherwise  =  listAEquiv isAEquivTV bvs1 bvs2 bij tsl1 tsl2
  where
    tsl1  = S.toList ts1
    tsl2  = S.toList ts2

isAEquivTV bvs1 bvs2 bij (v1,t1) (v2,t2)
 = do bij' <- isAEquivVar bvs1 bvs2 bij v1 v2
      isAEquiv bvs1 bvs2 bij' t1 t2
\end{code}

\newpage

List-variables replacing same:
\begin{code}
isAEquivLVarSub bvs1 bvs2 bij lvs1 lvs2
  | length lvl1 /= length lvl2 =  afail "lvar sublist lengths differ"
  | otherwise  =  listAEquiv isAEquivLVLV bvs1 bvs2 bij lvl1 lvl2
  where
    lvl1 = S.toList lvs1
    lvl2 = S.toList lvs2

isAEquivLVLV bvs1 bvs2 bij (tlv1,rlv1) (tlv2,rlv2)
  = do bij' <- isAEquivLVar bvs1 bvs2 bij tlv1 tlv2
       isAEquivLVar bvs1 bvs2 bij rlv1 rlv2
\end{code}

Doing it with lists:
\begin{code}
listAEquiv :: MonadFail m
           => ( VarSet -> VarSet -> (Map GenVar GenVar)
                -> a -> a
                -> m (Map GenVar GenVar) )
           -> VarSet -> VarSet -> (Map GenVar GenVar)
           -> [a] -> [a]
           -> m (Map GenVar GenVar)

listAEquiv aeqv bvs1 bvs2 bij [] [] = return bij
listAEquiv aeqv bvs1 bvs2 bij (t1:ts1) (t2:ts2)
 = do bij' <- aeqv bvs1 bvs2 bij t1 t2
      listAEquiv aeqv bvs1 bvs2 bij' ts1 ts2
listAEquiv _ _ _ _ _ _ = afail "thing lists differ"


checkAlphaBijections :: MonadFail m => (Map GenVar GenVar) -> [GenVar] -> [GenVar]
                     -> m (Map GenVar GenVar)

checkAlphaBijections bij [] [] = return bij
checkAlphaBijections bij (gv1:gvs1) (gv2:gvs2)
  = do bij' <- checkAlphaBijection bij gv1 gv2
       checkAlphaBijections bij' gvs1 gvs2
checkAlphaBijections _ _ _ = afail "bijection checks fail"
\end{code}


We define some failure shorthands:
\begin{code}
afail :: MonadFail m => String -> m a
afail why = fail ("not a-equiv: "++why)

afails :: MonadFail m => [String] -> m a
afails whys = afail $ unlines' whys
\end{code}


\begin{code}
tryAlphaEquivalence :: Term -> Term -> YesBut (Map GenVar GenVar)
tryAlphaEquivalence t1 t2  =  isAEquiv S.empty S.empty M.empty t1 t2
\end{code}