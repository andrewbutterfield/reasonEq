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
    where $\alpha$ is injective, and $\rng~\alpha \cap (V \cup fv(P)) = \emptyset$.
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
  \mathrm{inj}(\alpha)  \land \rng~\alpha \cap (V \cup \fv.P) = \emptyset
$$

We expect the \texttt{trm} argument to be a binder.
We check the injectivity.
\begin{code}
alphaRename :: Monad m => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                       -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                       -> Term -> m Term
alphaRename vvs lls (Bind tk n vs tm)
  =  do vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        bnd tk n (aRenVS vmap lmap vs) (aRenTRM vmap lmap tm)
alphaRename vvs lls (Lam  tk n vl tm)
  =  do vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        lam tk n (aRenVL vmap lmap vl) (aRenTRM vmap lmap tm)
alphaRename vvs lls trm = fail "alphaRename not applicable"


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

aRenTRM vmap lmap _ = error "aRenTRM NYI"
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
