\section{Free Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( freeVars
, SubAbility(..), SubAbilityMap
, alphaRename, quantSubstitute, quantNest
) where
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List
import Data.Maybe

import Utilities (injMap)
import LexBase
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
freeVars :: Term -> VarSet
freeVars (Var tk v)           =  S.singleton $ StdVar v
freeVars (Cons tk n ts)       =  S.unions $ map freeVars ts
freeVars (Bind tk n vs tm)    =  freeVars tm S.\\ vs
freeVars (Lam tk n vl tm)     =  freeVars tm S.\\ S.fromList vl
freeVars (Cls _ _)            =  S.empty
freeVars (Sub tk tm s)        =  (tfv S.\\ tgtvs) `S.union` rplvs
   where
     tfv            =  freeVars tm
     (tgtvs,rplvs)  =  substFree tfv s
freeVars (Iter tk na ni lvs)  =  S.fromList $ map LstVar lvs
freeVars _ = S.empty
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
   rplvs = S.unions (S.map (freeVars . snd) ts')
           `S.union`
           S.map (LstVar .snd) lvs'
\end{code}

A target/replacement pair is ``applicable'' if the target variable
is in the free variables of the term being substituted.
\begin{code}
applicable :: (tgt -> GenVar) -> VarSet -> (tgt,rpl) -> Bool
applicable wrap tfv (t,_) = wrap t `S.member` tfv
\end{code}

\newpage
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
In order to do this, we need to know which constructors are substitutable
(e.g, propostional operators, and UTP conditional $\_\cond{\_}\_$ are,
while assignment  $\_:=\_$ is not).
We explicitly capture this property:
\begin{code}
data SubAbility = CS -- Can Substitute
              | NS -- Not Substitutable
              deriving (Eq, Ord, Show, Read)
\end{code}
We maintain, per-theory,
a map from  \texttt{Cons} identifiers defined by that theory,
to their subsitutability.
In any given proof context we will have a list of such maps,
on for each theory in scope.
\begin{code}
type SubAbilityMap = Map Identifier SubAbility
\end{code}
We want to search a list of these maps, checking for substitutability
\begin{code}
isSubstitutable :: [SubAbilityMap] -> Identifier -> Bool
isSubstitutable [] n  =  False -- should never happen in well-defined theories
isSubstitutable (sam:sams) n
  = case M.lookup n sam of
      Nothing  ->  isSubstitutable sams n
      Just s   ->  s == CS
\end{code}
We also want to convert our $\alpha$ ``maps'' into
substitutions, when we encounter a non-substitutable constructor.
\begin{code}
alphaAsSubstn :: (Map Variable Variable)  -- (tgt.v -> rpl.v)
              -> (Map ListVar ListVar)      -- (tgt.lv -> rpl.lv)
              -> Substn
alphaAsSubstn vmap lmap
  = fromJust $ substn (M.assocs $ M.map varAsTerm vmap) $ M.assocs lmap
\end{code}

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
alphaRename :: Monad m => [SubAbilityMap]
                       -> ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                       -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                       -> Term -> m Term
alphaRename sams vvs lls (Bind tk n vs tm)
  =  do checkDomain vvs lls vs
        vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        bnd tk n (aRenVS vmap lmap vs) (aRenTRM sams vmap lmap tm)
alphaRename sams vvs lls (Lam  tk n vl tm)
  =  do checkDomain vvs lls (S.fromList vl)
        vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        lam tk n (aRenVL vmap lmap vl) (aRenTRM sams vmap lmap tm)
alphaRename sams vvs lls trm = fail "alphaRename not applicable"
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
     trmFV = freeVars trm
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

\newpage
\paragraph{$\mathbf\alpha$-Renaming Terms}
Top-level quantifier body and below.

Variables and and iterators are straightforward
\begin{code}
aRenTRM sams vmap lmap (Var  tk v)     =  fromJust $ var tk (aRenV vmap v)
aRenTRM sams vmap lmap (Iter tk na ni lvs)  =   Iter tk na ni $ map (aRenLV lmap) lvs
\end{code}
We need to check constructors for substitutability
\begin{code}
aRenTRM sams vmap lmap tm@(Cons tk n ts)
  | isSubstitutable sams n  =  Cons tk n $ map (aRenTRM sams vmap lmap) ts
  | otherwise               =  Sub tk tm $ alphaAsSubstn vmap lmap
\end{code}
Internal quantifiers screen out renamings%
\footnote{We wouldn't need this if we guaranteed no quantifier shadowing.}
.
\[
   (\mathsf{Q} V \bullet P)\alpha
   =
   (\mathsf{Q} V \bullet P(\alpha\setminus V))
\]
\begin{code}
aRenTRM sams vmap lmap (Bind tk n vs tm)
 = fromJust $ bnd tk n vs (aRenTRM sams vmap' lmap' tm)
 where vmap' = vmap `M.withoutKeys` (stdVarSetOf vs)
       lmap' = lmap `M.withoutKeys` (listVarSetOf vs)

aRenTRM sams vmap lmap (Lam  tk n vl tm)
 = fromJust $ lam tk n vl (aRenTRM sams vmap' lmap' tm)
 where vs = S.fromList vl
       vmap' = vmap `M.withoutKeys` (stdVarSetOf vs)
       lmap' = lmap `M.withoutKeys` (listVarSetOf vs)
\end{code}
Substitution is tricky \dots
\[
  (P[\lst e/\lst x])\alpha
  =
  (P(\alpha\setminus\lst x)[\lst e \alpha / \lst x]
\]
\begin{code}
aRenTRM sams vmap lmap (Sub tk tm (Substn ts lvs))
  = let

      (vl,tl) = unzip $ S.toList ts
      tl' = map (aRenTRM sams vmap lmap) tl
      tsl' = zip vl tl'

      (tvl,rvl) = unzip $ S.toList lvs
      rvl' = map (aRenLV lmap) rvl
      lvsl' = zip tvl rvl'

      suba = fromJust $ substn tsl' lvsl'

      subtgtvs  = S.fromList vl
      vmap' = vmap `M.withoutKeys` subtgtvs

      subtgtlvs = S.fromList tvl
      lmap' = lmap `M.withoutKeys` subtgtlvs

    in Sub tk (aRenTRM sams vmap' lmap' tm) suba
\end{code}
Everything else is unaffected.
\begin{code}
aRenTRM _ _ _ trm = trm  -- Val, Cls
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
