\section{$\alpha$ Equivalence}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2021-22

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

import YesBut
import Utilities
-- import Control
import LexBase
import Variables
import AST
import SideCond
import FreeVars
-- import VarData
-- import Binding
-- import Matching

import Debugger
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
\end{eqnarray*}
Equivalence is shown here in each case 
by proposing a bijective mapping of the form:
$$
 \setof{O_1 \mapsto O_4, O_2 \mapsto O_3}
$$
This makes it simple to implement a check for $\alpha$-equivalence.
We define a context that is a variable-variable bijective mapping $\beta$,
which leads to the following sequent:
$$
  \beta  \vdash  t_1 \aeqv t_2 \mapsto \beta'
$$
This describes a situation in which $\beta'$ is the desired bijection
that shows that $t_1$ and $t_2$ are $\alpha$-equivalent,
that is consistent with $\beta$.

So, at the top-level (no/empty context), $t_1$ is $\alpha$-equivalent to $t_2$ 
if we can derive 
$\epsilon \vdash t_1 \aeqv t_2 \mapsto \beta'$.
\begin{code}
isAlphaEquivalent :: Term -> Term -> Bool
isAlphaEquivalent t1 t2 = isJust $ isAEquiv M.empty t1 t2
(=~=)  =  isAlphaEquivalent
\end{code}


\newpage

\subsection{Term $\alpha$-Equivalence}

$$
  \beta  \vdash  t_1 \aeqv t_2 \mapsto \beta'
$$
The function below returns $\beta'$ if successful.

We maintain the bound variables and the bijection at the general variable level.
\begin{code}
isAEquiv :: MonadFail m 
         => (Map GenVar GenVar) -> Term -> Term -> m (Map GenVar GenVar)
\end{code}

\subsubsection{Value $\alpha$-equivalence}

Values must be equal:
$$
\inferrule%
  {\kk{k_1} = \kk{k_2}}
  {\beta \vdash \kk{k_1} \equiv_\alpha \kk{k_2} \mapsto \beta}
$$
\begin{code}
isAEquiv bij (Val tk1 k1) (Val tk2 k2)
  | tk1 == tk2 && k1 == k2  =  return bij
  | otherwise  =  afail "literal values differ"
\end{code}

\subsubsection{Variable $\alpha$-equivalence}

We check kinds, and if the same, hand over to a variable handling function.
\begin{code}
isAEquiv bij (Var tk1 v1) (Var tk2 v2)
  | tk1 /= tk2  =  afail "var kind differs"
  | otherwise   =  isAEquivVar bij v1 v2
\end{code}

\subsubsection{Constructor $\alpha$-equivalence}

Constructors must have the same number of sub-terms,
with the corresponding ones being equivalent:
$$
\inferrule%
  {      n_1=n_2 
    \and \kk k =\ell \and i \in 1\dots k
    \and \beta_i  \vdash  s_i \aeqv t_i
    \and \beta'=\beta\uplus\beta_1\uplus\dots\uplus\beta_k}
  { \beta
    \vdash  
    \cc {n_1} {s_1,\dots,s_k} 
    \aeqv \cc {n_2} {t_1,\dots,t_\ell} \mapsto \beta'
  }
$$
Here $\uplus$ merges $\beta$s, provided they agree on their overlap.
\begin{code}
isAEquiv bij (Cons tk1 sb1 n1 ts1) (Cons tk2 sb2 n2 ts2)
  | tk1 /= tk2  =  afail "cons kind differs"
  | sb1 /= sb2  =  afail "cons subable differs"
  | n1  /= n2   =  afail "cons name differs"
  | otherwise   =  listAEquiv isAEquiv bij ts1 ts2
\end{code}

\newpage

\subsubsection{Binder $\alpha$-equivalence}

When checking two binders, 
check the binding occurences first,
remove the binding occurences (if any) from the incoming binding
and adding the above check result.
and use the result check the terms .
Then discard the bound variables before computing the result bijection.
$$
\inferrule%
   {      n_1 = n_2
     \and (\beta_Q = v_1^+ \times v_2^+ \text{ is bijective})
     \and ( (\beta\setminus v_1^+)\uplus\beta_Q 
            \vdash 
            t_1 \aeqv t_2 \mapsto \beta_T )
   }
   { \beta 
     \vdash 
     (\bb {n_1} {v_1^+} {t_1}) 
     \aeqv 
     (\bb {n_2} {v_2^+} {t_2})
     \mapsto
     \beta \uplus (\beta_T \setminus v_1^t)
   }
$$
\begin{code}
isAEquiv bij (Bnd tk1 n1 vs1 tm1) (Bnd tk2 n2 vs2 tm2)
  | tk1        /= tk2         =  afail "bind kind differs"
  | n1         /= n2          =  afail "bind name differs"
  | S.size vs1 /= S.size vs2  =  afail "bind size differs"
  | otherwise =
      do let bijQ = M.fromList $ zip vl1 vl2
         bijQ' <- bijExtend bij' bijQ
         bijT <- isAEquiv bijQ' tm1 tm2
         let bijT' = M.filterWithKey (\k _ -> not(k `S.member` vs1)) bijT
         bijExtend bij bijT'
  where
    bij' = M.filterWithKey (\k _ -> not(k `S.member` vs1)) bij
    vl1 = S.toList vs1
    vl2 = S.toList vs2
\end{code}

\subsubsection{Lambda $\alpha$-equivalence}

Similar to above,
except that we have bound variable lists,
rather than sets.
$$
\inferrule%
   {      n_1 = n_2
     \and (\beta_Q = v_1^+ \times v_2^+ \text{ is bijective})
     \and ( (\beta\setminus v_1^+)\uplus\beta_Q 
            \vdash 
            t_1 \aeqv t_2 \mapsto \beta_T )
   }
   { \beta 
     \vdash 
     (\ll {n_1} {v_1^+} {t_1}) 
     \aeqv 
     (\ll {n_2} {v_2^+} {t_2})
     \mapsto
     \beta \uplus (\beta_T \setminus v_1^t)
   }
$$
\begin{code}
isAEquiv bij (Lam tk1 n1 vl1 tm1) (Lam tk2 n2 vl2 tm2)
  | tk1        /= tk2         =  afail "lambda kind differs"
  | n1         /= n2          =  afail "lambda name differs"
  | length vl1 /= length vl2  =  afail "lambda arity differs"
  | otherwise =
      do let bijQ = M.fromList $ zip vl1 vl2
         bijQ' <- bijExtend bij' bijQ
         bijT <- isAEquiv bijQ' tm1 tm2
         let bijT' = M.filterWithKey (\k _ -> not(k `elem` vl1)) bijT
         bijExtend bij bijT'
  where
    bij' = M.filterWithKey (\k _ -> not(k `elem` vl1)) bij
\end{code}

\newpage

\subsubsection{Closure $\alpha$-equivalence}

Closure is like bind, but where the \texttt{vs}$i$ cover all the
free-variables in the term.
We start body term analysis with an empty bijection,
and there are no free variables with changes that need to be returned.
$$
\inferrule%
   { n_1 = n_2  
     \and  
     (\beta \vdash
        (\bb {n_1} {\fv{(t_1)}} {t_1}) 
        \aeqv 
        (\bb {n_2} {\fv{(t_2)}} {t_2}) 
        \mapsto \beta' ) }
   { \beta 
     \vdash 
     \xx {n_1} {t_1}  \aeqv  \xx {n_2} {t_2}
     \mapsto
     \beta'
   }
$$
\begin{code}
isAEquiv bij (Cls n1 tm1) (Cls n2 tm2)
  | n1 /= n2  =  afail "closure name differs"
  | otherwise 
    = do all1 <- pBnd n1 vs1 tm1
         all2 <- pBnd n2 vs2 tm2
         isAEquiv bij all1 all2
  where
    vs1 = theFreeVars $ freeVars scTrue tm1  -- safe?
    vs2 = theFreeVars $ freeVars scTrue tm2  -- safe?
\end{code}

\subsubsection{Substitution $\alpha$-equivalence}

For substitution, first check the terms, then the substitution lists.
\begin{code}
isAEquiv bij (Sub tk1 tm1 s1) (Sub tk2 tm2 s2)
  | tk1 /= tk2  =  afail "substn kind differs"
  | otherwise =
      do bij' <- isAEquiv bij tm1 tm2
         isAEquivSub bij' s1 s2
\end{code}

\subsubsection{Iteration $\alpha$-equivalence}

For now, we consider the list-variables as free at this point.
\begin{code}
isAEquiv bij (Iter tk1 sa1 na1 si1 ni1 lvs1)
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
isAEquiv bij (VTyp typ1 v1) (VTyp typ2 v2)
  | typ1 /= typ2  =  afail "type-declaration types differ"
  | otherwise     =  isAEquivVar bij v1 v2
\end{code}

Everything else is a fail.
\begin{code}
isAEquiv _ _ _ = afail "term variants differ"
\end{code}

\newpage 

\subsection{Variable $\alpha$-equivalence}

Are two variables equivalent?
For $ \vv v_1 \aeqv \vv v_2 $ , we have two cases:

$$
\inferrule%
  { \vv v_1 \notin \dom\beta
    \and
    \vv v_2 = \vv v_1
  }
  { \beta  \vdash  \vv{v}_1 \aeqv \vv{v}_2 \mapsto \beta}
$$
$$
\inferrule%
  { \vv v_1 \in \dom\beta
    \and
    \vv v_2 = \beta(\vv v_1)
  }
  { \beta  \vdash  \vv{v}_1 \aeqv \vv{v}_2 \mapsto \beta}
$$

\begin{code}
isAEquivGVar :: MonadFail m 
            => (Map GenVar GenVar) -> GenVar -> GenVar 
            -> m (Map GenVar GenVar)

isAEquivVar  bij v1  v2   =  isAEquivGVar bij (StdVar v1 ) (StdVar v2 )
isAEquivLVar bij lv1 lv2  =  isAEquivGVar bij (LstVar lv1) (LstVar lv2)
isAEquivGVar bij gv1 gv2
  | notAlphaCompatible gv1 gv2  =  afails "not compatible" dump
  | gv1 `M.member` bij
      = case M.lookup gv1 bij of
          Just gv2' -> if gv2' == gv2
                       then return bij
                       else afail "bound var is different"
          Nothing   -> afail "bij map broken"
  | gv1 == gv2  =  return bij
  | otherwise   =  afails "different free variables" dump
  where
    dump = [ "gv1 = "++show gv1 
           , "gv2 = "++show gv2
           , "bij = "++show bij
           ]
\end{code}

Given a bijection, and two (bound) general variables,
see if they are already noted, and add if not.
Fail if they are mismatched.
\begin{code}
checkAlphaBijection :: MonadFail m => (Map GenVar GenVar) -> GenVar -> GenVar
                    -> m (Map GenVar GenVar)

checkAlphaBijection bij gv1 gv2
  | notAlphaCompatible gv1 gv2  =  afails "gen-var not compatible" dump
  | otherwise                   =  extdBij bij gv1 gv2
  where
    dump = [ "gv1 = "++show gv1 
           , "gv2 = "++show gv2
           , "bij = "++show bij
           ]
\end{code}

A bound variable can match a different bound variable,
provided that the only difference is the variable identifier
or a \texttt{During} subscript.
\begin{code}
notAlphaCompatible (StdVar (Vbl _ class1 when1))
                   (StdVar (Vbl _ class2 when2))
  =  class1 /= class2  ||  notCompatibleWhen when1 when2
notAlphaCompatible (LstVar (LVbl (Vbl _ class1 when1) is1 js1) )
                   (LstVar (LVbl (Vbl _ class2 when2) is2 js2) )
  =  class1 /= class2  ||  notCompatibleWhen when1 when2
     || is1 /= is2 || js1 /= js2
notAlphaCompatible _ _ = True

notCompatibleWhen (During _) (During _)  =  False
notCompatibleWhen when1      when2       =  when1 /= when2
\end{code}

\subsection{Substitution $\alpha$-equivalence}

With substitution we check the two sub-component pair-lists.
\begin{code}
isAEquivSub bij (Substn ts1 lvs1) (Substn ts2 lvs2)
  = do bij' <- isAEquivTermSub bij ts1 ts2
       isAEquivLVarSub bij' lvs1 lvs2
\end{code}

Terms replacing variables:
\begin{code}
isAEquivTermSub bij ts1 ts2
  | length tsl1 /= length tsl2 =  afail "term sublist lengths differ"
  | otherwise  =  listAEquiv isAEquivTV bij tsl1 tsl2
  where
    tsl1  = S.toList ts1
    tsl2  = S.toList ts2

isAEquivTV bij (v1,t1) (v2,t2)
 = do bij' <- isAEquivVar bij v1 v2
      isAEquiv bij' t1 t2
\end{code}

List-variables replacing same:
\begin{code}
isAEquivLVarSub bij lvs1 lvs2
  | length lvl1 /= length lvl2 =  afail "lvar sublist lengths differ"
  | otherwise  =  listAEquiv isAEquivLVLV bij lvl1 lvl2
  where
    lvl1 = S.toList lvs1
    lvl2 = S.toList lvs2

isAEquivLVLV bij (tlv1,rlv1) (tlv2,rlv2)
  = do bij' <- isAEquivLVar bij tlv1 tlv2
       isAEquivLVar bij rlv1 rlv2
\end{code}

Doing it with lists:
\begin{code}
listAEquiv :: MonadFail m
           => ( (Map GenVar GenVar)
                -> a -> a
                -> m (Map GenVar GenVar) )
           -> (Map GenVar GenVar)
           -> [a] -> [a]
           -> m (Map GenVar GenVar)

listAEquiv aeqv bij [] [] = return bij
listAEquiv aeqv bij (t1:ts1) (t2:ts2)
 = do bij' <- aeqv bij t1 t2
      listAEquiv aeqv bij' ts1 ts2
listAEquiv _ _ _ _ = afail "thing lists differ"


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

afails :: MonadFail m => String -> [String] -> m a
afails why dump = afail $ unlines' (why:dump)
\end{code}


\begin{code}
tryAlphaEquivalence :: Term -> Term -> YesBut (Map GenVar GenVar)
tryAlphaEquivalence t1 t2  =  isAEquiv M.empty t1 t2
\end{code}