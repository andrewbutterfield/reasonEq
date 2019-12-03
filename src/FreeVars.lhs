\section{Free Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( termFree
, alphaRename, quantSubstitute, quantNest
) where
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List
import Data.Maybe

import Utilities (injMap)
import Variables
import AST

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

\subsection{Introduction}

We start with computing the free variables of a term,
and then continue by addressing key functions associated
with quantifiers.


\subsection{Term Free Variables}

\begin{eqnarray*}
   \fv(\kk k)  &\defs&  \emptyset
\\ \fv(\vv v)  &\defs&  \{\vv v\}
\\ \fv(\cc n {ts}) &\defs& \bigcup_{t \in ts} \fv(ts)
\\ \fv(\bb n {v^+} t) &\defs& \fv(t)\setminus{v^+}
\\ \fv(\ll n {v^+} t) &\defs& \fv(t)\setminus{v^+}
\\ \fv(\ss t {v^n} {t^n})
   &\defs&
   (\fv(t)\setminus{v^m})\cup \bigcup_{s \in t^m}\fv(s)
\\ \textbf{where} && v^m = v^n \cap \fv(t), t^m \textrm{ corr. to } v^m
\\ \fv(\ii \bigoplus n {lvs}) &\defs& lvs
\end{eqnarray*}

\begin{code}
termFree :: Term -> VarSet
termFree (Var tk v)           =  S.singleton $ StdVar v
termFree (Cons tk n ts)       =  S.unions $ map termFree ts
termFree (Bind tk n vs tm)    =  termFree tm S.\\ vs
termFree (Lam tk n vl tm)     =  termFree tm S.\\ S.fromList vl
termFree (Cls _ _)            =  S.empty
termFree (Sub tk tm s)        =  (tfv S.\\ tgtvs) `S.union` rplvs
   where
     tfv            =  termFree tm
     (tgtvs,rplvs)  =  substFree tfv s
termFree (Iter tk na ni lvs)  =  S.fromList $ map LstVar lvs
termFree _ = S.empty
\end{code}

\newpage
\subsubsection{Substitution Free Variables}

Substitution is complicated, so here's a reminder:
\begin{eqnarray*}
   \fv(\ss t {v^n} {t^n})
   &\defs&
   (\fv(t)\setminus{v^m})\cup \bigcup_{s \in t^m}\fv(s)
\\ \textbf{where} && v^m = v^n \cap \fv(t), t^m \textrm{ corr. to } v^m
\end{eqnarray*}
\begin{code}
substFree tfv (Substn ts lvs) = (tgtvs,rplvs)
 where
   ts' = S.filter (applicable StdVar tfv) ts
   lvs' = S.filter (applicable LstVar tfv) lvs
   tgtvs = S.map (StdVar . fst) ts'
           `S.union`
           S.map (LstVar . fst) lvs'
   rplvs = S.unions (S.map (termFree . snd) ts')
           `S.union`
           S.map (LstVar .snd) lvs'
\end{code}

A target/replacement pair is ``applicable'' if the target variable
is in the free variables of the term being substituted.
\begin{code}
applicable :: (tgt -> GenVar) -> VarSet -> (tgt,rpl) -> Bool
applicable wrap tfv (t,_) = wrap t `S.member` tfv
\end{code}

\subsection{Quantifier Handling}

We have an abstract syntax that singles out quantifiers
($\mathsf{Q} x,y,\dots \bullet P$),
which occur in two basic forms,
one ($\Gamma \setof{x,y,\dots} \bullet P$) based on variable sets,
the other ($\Lambda \seqof{x,y,\dots} \bullet P$) based on variable lists.
Here we provide transformations that we expect to be able to apply
all such quantified forms:
\begin{description}
  \item [$\alpha$-renaming]~\\
    $
      \mathsf{Q} V \bullet P
      =
      \mathsf{Q} V\alpha \bullet P\alpha
    $
    where $\alpha$ is injective, $\dom~\alpha \subseteq V$,
    and $\rng~\alpha \cap (V \cup fv(P)) = \emptyset$.
  \item [Substitution]~\\
      $
        (\mathsf{Q} V \bullet P)[Q/U]
        =
        \mathsf{Q} V \bullet P[Q'/(U\setminus V)]
      $
      where $Q'$ are parts of $Q$ corresponding to $U\setminus V$.
  \item [Nesting]~\\
     Only applicable when variable-sets are used in a quantifier:\\
     $
       (\Gamma_i V_i \bullet \Gamma_j V_j \bullet P)
       =
       (\Gamma_i (V_i\setminus V_j) \bullet \Gamma_j V_j \bullet P)
     $
\end{description}

\newpage
\subsubsection{$\alpha$-Renaming}

$$
  \mathsf{Q} V \bullet P
  =
  \mathsf{Q} V\alpha \bullet P\alpha
  ,\quad
  \mathrm{inj}(\alpha)  \land \dom~\alpha \subseteq V \land \rng~\alpha \cap (V \cup \fv.P) = \emptyset
$$

We expect the \texttt{trm} argument to be a binder.
We check the injectivity, and freshness.
\begin{code}
alphaRename :: Monad m => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                       -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                       -> Term -> m Term
alphaRename vvs lls (Bind tk n vs tm)
  =  do checkDomain vvs lls vs
        vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        bnd tk n (aRenVS vmap lmap vs) (aRenTRM vmap lmap tm)
alphaRename vvs lls (Lam  tk n vl tm)
  =  do checkDomain vvs lls (S.fromList vl)
        vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        lam tk n (aRenVL vmap lmap vl) (aRenTRM vmap lmap tm)
alphaRename vvs lls trm = fail "alphaRename not applicable"
\end{code}

\paragraph{Domain Checking}~

\begin{code}
checkDomain :: Monad m => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                       -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                       -> VarSet
                       -> m ()
checkDomain vvs lls qvs
 = let
     alphaDom = (S.fromList $ map (StdVar . fst) vvs)
                `S.union`
                (S.fromList $ map (LstVar . fst) lls)
   in if S.null (alphaDom S.\\ qvs)
       then return ()
       else fail "alphaRename: trying to rename free variables."
\end{code}

\paragraph{Freshness Checking}~

\begin{code}
checkFresh :: Monad m => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                      -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                      -> Term
                      -> m ()
checkFresh vvs lls trm
 = let
     trmFV = termFree trm
     alphaRng = (S.fromList $ map (StdVar . snd) vvs)
                `S.union`
                (S.fromList $ map (LstVar . snd) lls)
   in if S.null (trmFV `S.intersection` alphaRng)
       then return ()
       else fail "alphaRename: new bound-vars not fresh"
\end{code}

\newpage
\paragraph{$\mathbf\alpha$-Renaming (many) Variables}~

\begin{code}
aRenVS vmap lmap  =  S.fromList . aRenVL vmap lmap . S.toList

aRenVL vmap lmap vl = map (aRenGV vmap lmap) vl

aRenGV vmap lmap (StdVar  v)  =  StdVar $ aRenV  vmap v
aRenGV vmap lmap (LstVar lv)  =  LstVar $ aRenLV lmap lv

aRenV vmap v
  = case M.lookup v vmap of
      Nothing   ->  v
      Just v'   ->  v'

aRenLV lmap lv
  = case M.lookup lv lmap of
      Nothing   ->  lv
      Just lv'  ->  lv'
\end{code}


\paragraph{$\mathbf\alpha$-Renaming Terms}
Top-level quantifier body and below.

Variables and constructors and iterators are straightforward
\begin{code}
aRenTRM vmap lmap (Var  tk v)     =  fromJust $ var tk (aRenV vmap v)
aRenTRM vmap lmap (Cons tk n ts)  =  Cons tk n $ map (aRenTRM vmap lmap) ts
aRenTRM vmap lmap (Iter tk na ni lvs)  =   Iter tk na ni $ map (aRenLV lmap) lvs
\end{code}
Internal quantifiers screen out renamings.
\[
   (\mathsf{Q} V \bullet P)\alpha
   =
   (\mathsf{Q} V \bullet P(\alpha\setminus V))
\]
We wouldn't need this if we guaranteed no quantifier shadowing.
\begin{code}
aRenTRM vmap lmap (Bind tk n vs tm)
 = fromJust $ bnd tk n vs (aRenTRM vmap' lmap' tm)
 where vmap' = vmap `M.withoutKeys` (stdVarSetOf vs)
       lmap' = lmap `M.withoutKeys` (listVarSetOf vs)

aRenTRM vmap lmap (Lam  tk n vl tm)
 = fromJust $ lam tk n vl (aRenTRM vmap' lmap' tm)
 where vs = S.fromList vl
       vmap' = vmap `M.withoutKeys` (stdVarSetOf vs)
       lmap' = lmap `M.withoutKeys` (listVarSetOf vs)
\end{code}
Substitution is tricky \dots
\[
  (P\sigma)\alpha
  =
  ?
\]
\begin{code}
-- aRenTRM vmap lmap (Sub tk tm s) = Sub tk tma sa
\end{code}
Everything else is unaffected.
\begin{code}
aRenTRM _ _ trm = trm  -- Val, Cls
\end{code}

\newpage
\subsubsection{Substitution}

$$
  (\mathsf{Q} V \bullet P)[Q/U]
  =
  \mathsf{Q} V \bullet P[Q'/(U\setminus V)]
$$ where $Q'$ are parts of $Q$ corresponding to $U\setminus V$.

Again, we require that \texttt{trm}
is a binder.
\begin{code}
quantSubstitute :: Monad m => Substn -> Term -> m Term
quantSubstitute sub (Bind tk n vs tm) = fail "quantSubstitute Bind NYI"
quantSubstitute sub (Lam  tk n vl tm) = fail "quantSubstitute Lam NYI"
quantSubstitute sub t = fail "quantSubstitute not applicable"
\end{code}

\newpage
\subsubsection{Nesting}

$$
 (\Gamma_i V_i \bullet \Gamma_j V_j \bullet P)
 =
 (\Gamma_i (V_i\setminus V_j) \bullet \Gamma_j V_j \bullet P)
$$

Here, we require that \texttt{trm} is a \texttt{Bind}.
\begin{code}
quantNest :: Monad m => Term -> m Term
quantNest (Bind tk n vs tm) = fail "quantNest Bind NYI"
quantNest t = fail "quantNest not applicable"
\end{code}
