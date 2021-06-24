\section{Instantiate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Instantiate
( instantiate
, instVarSet
, instASCVariant
, instantiateSC
) where
import Data.Maybe
-- import Data.Either (lefts,rights)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List

import Utilities
import LexBase
import Variables
import AST
import SideCond
import Binding
import FreeVars
import VarData
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\subsection{Introduction}

We take a pattern term and a binding
and produce a re-constructed candidate term,
provided every variable in the pattern is also in the binding.
If $\beta$ is a binding, and $t$ is a term,
we use $\beta.t$ to denote the result of this instantiation.
Given a variable $v$ we use $\beta(v)$ to denote a binding lookup.

\begin{eqnarray*}
   \beta.\kk k &=& \kk k
\\ \beta.(\vv v) &=& \beta(v)
\\ \beta.(\cc n {ts}) &=& \cc n {(\beta^*.ts)}
\\ \beta.(\bb n {v^+} t) &=& \bb n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ll n {v^+} t) &=& \ll n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ss t {v^n} {t^n}) &=& \ss {\beta.t} {\beta^*(v^n)} {\beta^*.t^n}
\\ \beta.(\xx n t) &=& \xx {n} {\beta.t}
\\ \beta.(\tt \tau) &=& \tt \tau
\\ \beta.(\bigoplus(p)\seqof{\lst l^1,\dots,\lst l^a})
   &=& I\seqof{g^1_1,\dots,g^a_1}
       \oplus\dots\oplus
       I\seqof{g^1_i,\dots,g^a_i}
       \oplus\dots\oplus
       I\seqof{g^1_n,\dots,g^a_n}
\\ \where
\\ \beta &=& \beta' \oplus
             \setof{ \lst l^1 \mapsto \seqof{g^1_1,\dots,g^1_n}
                   , \dots
                   , \lst l^a \mapsto \seqof{g^a_1,\dots, g^a_n}
                   }
\\ I\seqof{v^1_i,\dots,v^a_i} &=& p(v^1_i,\dots,v^a_i)
\\ I\seqof{\lst l^1_i,\dots,\lst l^a_i}
   &=& \bigoplus(p)\seqof{\lst l^1_i,\dots,\lst l^a_i}
\end{eqnarray*}


\newpage
\subsection{Instantiating Term with a (Total) Binding}

Here werequire every free variable in the term to be also in the binding.
\begin{code}
instantiate :: Monad m => Binding -> Term -> m Term
\end{code}

\begin{eqnarray*}
   \beta.\kk k &=& \kk k
\\ \beta.\tt \tau &=& \tt \tau
\end{eqnarray*}
\begin{code}
instantiate binding v@(Val _ _)  =  return v
instantiate binding t@(Typ _)    =  return t
\end{code}

\begin{eqnarray*}
   \beta.(\vv v) &=& \beta(v)
\end{eqnarray*}
\begin{code}
instantiate binding vt@(Var tk v)
  = case lookupVarBind binding v of
      Just (BindVar v')   ->  var tk v'
      Just (BindTerm t')  ->  return t'
      Nothing             ->  fail $ unlines
                                     [ "instantiate: variable not found"
                                     , "var = " ++ trVar v
                                     , "bind = " ++ trBinding binding
                                     ]
\end{code}

\begin{eqnarray*}
   \beta.(\cc n {ts}) &=& \cc n {(\beta^*.ts)}
\end{eqnarray*}
\begin{code}
instantiate binding (Cons tk sb n ts)
  = fmap (Cons tk sb n) $ sequence $ map (instantiate binding) ts
\end{code}

\begin{eqnarray*}
   \beta.(\bb n {v^+} t) &=& \bb n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ll n {v^+} t) &=& \ll n {\beta^*.v^+} {\beta.t}
\end{eqnarray*}
\begin{code}
instantiate binding (Bnd tk n vs tm)
  = do vs' <- fmap theFreeVars $ instVarSet binding vs
       tm' <- instantiate binding tm
       bnd tk n vs' tm'
instantiate binding (Lam tk n vl tm)
  = do vl' <- instVarList binding vl
       tm' <- instantiate binding tm
       lam tk n vl' tm'
\end{code}

\begin{eqnarray*}
   \beta.(\xx n t) &=& \xx {n} {\beta.t}
\end{eqnarray*}
\begin{code}
instantiate binding (Cls n tm)
  = do tm' <- instantiate binding tm
       return $ Cls n tm'
\end{code}

\begin{eqnarray*}
   \beta.(\ss t {v^n} {t^n}) &=& \ss {\beta.t} {\beta^*(v^n)} {\beta^*.t^n}
\end{eqnarray*}
\begin{code}
instantiate binding (Sub tk tm s)
  = do tm' <- instantiate binding tm
       s' <- instSub binding s
       return $ Sub tk tm' s'
\end{code}

\begin{eqnarray*}
   \beta.(\bigoplus(p)\seqof{\lst l^1,\dots,\lst l^a})
   &=& I\seqof{g^1_1,\dots,g^a_1}
       \oplus\dots\oplus
       I\seqof{g^1_i,\dots,g^a_i}
       \oplus\dots\oplus
       I\seqof{g^1_n,\dots,g^a_n}
\\ \where
\\ \beta &=& \beta' \oplus
             \setof{ \lst l^1 \mapsto \seqof{g^1_1,\dots,g^1_n}
                   , \dots
                   , \lst l^a \mapsto \seqof{g^a_1,\dots, g^a_n}
                   }
\\ I\seqof{v^1_i,\dots,v^a_i} &=& p(v^1_i,\dots,v^a_i)
\\ I\seqof{\lst l^1_i,\dots,\lst l^a_i}
   &=& \bigoplus(p)\seqof{\lst l^1_i,\dots,\lst l^a_i}
\end{eqnarray*}
Note that all lists must be of the same length,
and at any list position $i$, the general variables $g^1_i, \dots, g^a_i$
are of the same type (std/list).
\begin{code}
instantiate binding (Iter tk sa na si ni lvs)
  = do lvtss <- instIterLVS binding lvs
       -- all have same non-zero length
       -- have the same kind of object (list-var/term)
       case lvtss of
         [lvts]  ->  return $ mkI lvts
         _       ->  return $ Cons tk sa na $ map mkI lvtss
  where
    mkI :: [LVarOrTerm] -> Term
    mkI lvts@(Right _:_) = Cons tk si ni $ tmsOf lvts
    mkI lvts@(Left  _:_) = Iter tk sa na si ni $ lvsOf lvts
\end{code}

So, below, we want to return
$
\seqof{
 \seqof{g^1_1,\dots,g^a_1}
 ,
 \dots
 ,
 \seqof{g^1_i,\dots,g^a_i}
 ,
 \dots
 ,
 \seqof{g^1_n,\dots,g^a_n}
}
$
\begin{code}
instIterLVS :: Monad m => Binding -> [ListVar] -> m [[LVarOrTerm]]
instIterLVS binding lvs
  = do lvtss <- sequence $ map (instTLGVar binding) lvs
       let lvtss' = transpose lvtss
       checkAndGroup arity [] lvtss'
       -- fail "instIterLVS NYI"
  where
    arity = length lvs
\end{code}

\begin{code}
instTLGVar :: Monad m => Binding -> ListVar -> m [LVarOrTerm]
instTLGVar binding lv
  = case lookupLstBind binding lv of
      Nothing              ->  return $ [injLV lv]  -- maps to self !
      Just (BindList vl')  ->  return $ map injGV vl'
      Just (BindTLVs tlvs) ->  return tlvs
      _ -> fail "instTLGVar: bound to sets."

injV :: Variable -> LVarOrTerm
injV = injTM . var2term
injGV :: GenVar -> LVarOrTerm
injGV (StdVar v)   =  injV v
injGV (LstVar lv)  =  injLV lv
\end{code}

\begin{code}
checkAndGroup :: Monad m => Int -> [[LVarOrTerm]] -> [[LVarOrTerm]]
              -> m [[LVarOrTerm]]
checkAndGroup a sstvl [] = return $ reverse sstvl
checkAndGroup a sstvl (lvts:lvtss)
 | length lvts /= a  =  fail $ unlines
                        [ "instIterLVS: wrong arity, expected "++show a
                        , "lvts = " ++ trLstLVarOrTerm lvts
                        ]
 | null lvs  =  checkAndGroup a (map injTM ts:sstvl)  lvtss
 | null ts   =  checkAndGroup a (map injLV lvs:sstvl) lvtss
 | otherwise  =  fail $ unlines
                  [ "instIterLVS: mixed var types"
                  , "lvts = " ++ trLstLVarOrTerm lvts
                  ]
 where
   (lvs,ts) = lvtmSplit lvts
\end{code}


\newpage
\paragraph{Instantiating Substitutions}

We expect the substitution target and replacement list-variables
to be bound to variable-lists, and not sets.
These lists should themselves only contain list-variables,
and for any target/replacement pair these lists will be of the same length.
\begin{code}
instSub :: Monad m => Binding -> Substn -> m Substn
instSub binding (Substn ts lvs)
  = do ts'  <- instZip (instStdVar binding)  (instantiate binding) (S.toList ts)
       ts'' <- sequence $ map getTheTargetVar ts'
       lvss' <- instZip (instLLVar binding) (instLLVar binding) (S.toList lvs)
       let (lvts,lvrs) = unzip lvss'
       let lvs' = zip (concat lvts) (concat lvrs)
       substn ts'' lvs'

instZip inst1 inst2 pairs
  = sequence $ map (instPair inst1 inst2) pairs
  where
    instPair inst1 inst2 (thing1,thing2)
      = do thing1' <- inst1 thing1
           thing2' <- inst2 thing2
           return (thing1',thing2')

getTheTargetVar :: Monad m => (FreeVars,Term) -> m (Variable,Term)
getTheTargetVar (fvs,tm)
  = do v' <- getTheVar fvs
       return (v',tm)

getTheVar :: Monad m => FreeVars -> m Variable
getTheVar fvs@(vs,diffs)
  = case S.toList vs of
      [StdVar v] | null diffs  ->  return v
      _  -> fail ("getTheVar: expected a single variable, not "++show fvs)
\end{code}

This code is used for list-var in substitutions only.
\begin{code}
instLLVar :: Monad m => Binding -> ListVar -> m [ListVar]
instLLVar binding lv
  = case lookupLstBind binding lv of
      Just (BindList vl')  ->  fromGVarToLVar vl'
      Just (BindSet  vs')  ->  fromGVarToLVar $ S.toList vs'
      Just (BindTLVs tlvs)
        | null ts          ->  return lvs
        | otherwise        ->  fail $ unlines
                                     [ "instLLVar: l-var bound to terms"
                                     , "l-var = " ++ trLVar lv
                                     , "bind = " ++ trBinding binding
                                     ]
        where (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
      Nothing              ->  fail $ unlines
                                     [ "instLLVar: l-var not found"
                                     , "l-var = " ++ trLVar lv
                                     , "bind = " ++ trBinding binding
                                     ]

fromGVarToLVar :: Monad m => VarList -> m [ListVar]
fromGVarToLVar [] = return []
fromGVarToLVar (StdVar v:vl)
 = fail ("fromGVarToLVar: Std variable found - " ++ show v)
fromGVarToLVar (LstVar lv:vl)
  = do lvs <- fromGVarToLVar vl
       return (lv:lvs)
\end{code}

\newpage
\paragraph{Instantiate Variable Collections}

The following code needs updating to handle free-variables properly.

Let $g$ denote a general variable, and $G$ a set of same.
\begin{eqnarray*}
   \beta.G &=& \textstyle \bigcup_{g \in G} \beta.g
\end{eqnarray*}
\begin{code}
instVarSet :: Monad m => Binding -> VarSet -> m FreeVars
instVarSet binding vs
  = do fvss <- sequence $ map (instGVar binding) $ S.toList vs
       return $ mrgFreeVarList fvss
\end{code}



For a general variable:
\begin{eqnarray*}
   \beta.v &=& \beta(v)
\\ \beta.T &=& \fv(\beta(T))
\\ \beta.\lst g &=& \beta(\lst g)
\end{eqnarray*}
\begin{code}
instGVar :: Monad m => Binding -> GenVar -> m FreeVars
instGVar binding (StdVar v)  = instStdVar binding v
instGVar binding (LstVar lv) = instLstVar binding lv
\end{code}

\begin{code}
instStdVar :: Monad m => Binding -> Variable -> m FreeVars
instStdVar binding v
  = case lookupVarBind binding v of
      Nothing             ->  return $ single v  -- maps to self !
      Just (BindVar v')   ->  return $ single v'
      Just (BindTerm t')  ->  return $ freeVars t'
      _  ->  fail "instStdVar: bound to identifier."
  where single v = (S.singleton (StdVar v),[])
\end{code}

\begin{code}
instLstVar :: Monad m => Binding -> ListVar -> m FreeVars
instLstVar binding lv
  = case lookupLstBind binding lv of
      Nothing              ->  return $ single lv  -- maps to self !
      Just (BindList vl')  ->  return (S.fromList vl',[])
      Just (BindSet  vs')  ->  return (vs',[])
      Just (BindTLVs tlvs)
        | null ts          ->  return (S.fromList $ map LstVar lvs,[])
        | otherwise        ->  fail "instLstVar: bound to terms."
        where (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
  where
    single lv = (S.singleton (LstVar lv),[])
\end{code}



With $L$ a list of general variables
\begin{eqnarray*}
   \beta.L &=& \mathsf{concat}_{g \in L} \beta.g
\end{eqnarray*}
\begin{code}
instVarList :: Monad m => Binding -> VarList -> m VarList
instVarList binding vl
  = fmap concat $ sequence $ map (instLGVar binding) vl
\end{code}
We do not expect these to map to terms.
\begin{code}
instLGVar :: Monad m => Binding -> GenVar -> m VarList
instLGVar binding (StdVar v)
  =  do fvs' <- instStdVar binding v
        v' <- getTheVar fvs'
        return [StdVar v]
instLGVar binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return [gv]  -- maps to self !
      Just (BindList vl')  ->  return vl'
      _ -> fail "instLGVar: bound to sets or terms."
\end{code}

\newpage
\subsection{Side-Condition Instantiation (Total)}

Doing it again, with side-conditions.
Bascially we drill down to the atomic side-conditions,
instantiate and simplify those,
and merge together.

\begin{code}
instantiateSC :: Monad m => Binding -> SideCond -> m SideCond
\end{code}
For atomic side-conditions:
\begin{eqnarray*}
   \beta.(D \disj  T) &=& \beta.D \disj \fv(\beta(T))
\\ \beta.(C \supseteq T)  &=& \beta.C \supseteq \fv(\beta(T))
\\ \beta(pre \supseteq T) &=& pre \supseteq \fv(\beta(T))
\end{eqnarray*}
For now, we assume that $\beta.C$, $\beta.D$
never result in terms,
and hence have no explicit $F_i\setminus B_i$ components.
This is true for any current%
\footnote{
 Theories \texttt{ForAll}, \texttt{Exists}, and \texttt{UClose}.
}
side-conditions.
The most sensible thing to do is to compute $\fv(\beta(T))$,
and then use $\beta.C$ or $\beta.D$
to try to eliminate any use of set difference.
\begin{code}
instantiateSC bind (ascs,freshvs)
  = do ascss' <- sequence $ map (instantiateASC bind) ascs
       freshvs' <- instVarSet bind freshvs
       mkSideCond (concat ascss') $ theFreeVars freshvs'
\end{code}
We compute $\beta.C$/$\beta.D$ first, failing (for now), if it has terms,
and then we compute  $\fv(\beta(T))$.
\begin{code}
instantiateASC :: Monad m => Binding -> AtmSideCond -> m [AtmSideCond]
instantiateASC bind asc
  = do (vsCD,diffs) <- instVarSet bind $ ascVSet asc
       if null diffs
         then instASCVariant vsCD fvsT asc
         else fail "instantiateASC: explicit diffs in var-set not handled."
  where
     fvsT = instantiateGVar bind $ ascGVar asc
\end{code}

\begin{code}
instASCVariant :: Monad m
               => VarSet -> FreeVars -> AtmSideCond -> m [AtmSideCond]
instASCVariant vsD fvT (Disjoint _ _)  =  instDisjoint vsD fvT
instASCVariant vsC fvT (Covers _ _)    =  instCovers   vsC fvT
instASCVariant _   fvT (IsPre _)       =  instIsPre        fvT
\end{code}


\subsubsection{Disjointedness}

\begin{eqnarray*}
   \beta.(D \disj  T) &=& \beta.D \disj \fv(\beta(T))
\\ &=& \beta.D \disj (F \cup \{F_i\setminus B_i\}_{i \in 1\dots N})
\\ &=& \beta.D \disj F \land \{\beta.D \disj (F_i\setminus B_i)\}_{i \in 1\dots N}
\\ &=& \beta.D \disj F \land \{(\beta.D\setminus B_i) \disj F_i\}_{i \in 1\dots N}
\end{eqnarray*}
where $\fv(\beta(T)) = F \cup \{F_i\setminus B_i\}_{i \in 1\dots N}$,
$F \disj F_i$, $F \disj B_i$.
\begin{code}
instDisjoint :: Monad m => VarSet -> FreeVars -> m [AtmSideCond]
instDisjoint vsD (fF,fLessBs)
  =  return (asc1 ++ concat asc2)
  where
    asc1 = map (f1 vsD) (S.toList fF)
    asc2 = map (f2 vsD) fLessBs
    f1 vsD gv = Disjoint gv vsD
    f2 vsD (vsF,vsB) = map (f1 (vsD S.\\ vsB)) (S.toList vsF)
\end{code}

\subsubsection{Covering}

\begin{eqnarray*}
   \beta.(C \supseteq T)
   &=& \beta.C \supseteq \fv(\beta(T))
\\ &=& \beta.C \supseteq (F \cup \{F_i\setminus B_i\}_{i \in 1\dots N})
\\ &=& \beta.C \supseteq F \land \{\beta.C \supseteq (F_i\setminus B_i)\}_{i \in 1\dots N}
\\ &=& \beta.C \supseteq F \land \{(\beta.C \cup B_i) \supseteq F_i\}_{i \in 1\dots N}
\end{eqnarray*}
where $\fv(\beta(T)) = F \cup \{F_i\setminus B_i\}_{i \in 1\dots N}$,
$F \disj F_i$, $F \disj B_i$.
\begin{code}
instCovers :: Monad m => VarSet -> FreeVars -> m [AtmSideCond]
instCovers vsC (fF,fLessBs)
  =  return (asc1 ++ concat asc2)
  where
    asc1 = map (f1 vsC) (S.toList fF)
    asc2 = map (f2 vsC) fLessBs
    f1 vsC gv = Covers gv vsC
    f2 vsC (vsF,vsB) = map (f1 (vsC `S.union` vsB)) (S.toList vsF)
\end{code}



\subsubsection{Pre-Condition}

\begin{eqnarray*}
   \beta(pre \supseteq T)
   &=& pre \supseteq \fv(\beta(T))
\\ &=& pre \supseteq (F \cup \{F_i\setminus B_i\}_{i \in 1\dots N})
\\ &=& pre \supseteq F \land \{pre (F_i\setminus B_i)\}_{i \in 1\dots N}
\end{eqnarray*}
where $\fv(\beta(T)) = F \cup \{F_i\setminus B_i\}_{i \in 1\dots N}$,
$F \disj F_i$, $F \disj B_i$.
\begin{code}
instIsPre :: Monad m => FreeVars -> m [AtmSideCond]
instIsPre  (fF,fLessBs)
  =  return (asc1 ++ concat asc2)
  where
    asc1 = map IsPre (S.toList fF)
    asc2 = map f2 fLessBs
    f2 (vsF,vsB) = map IsPre $ S.toList (vsF S.\\ vsB)
\end{code}


\subsubsection{Side-condition Variable Instantiation}

Instantiate a (std./list)-variable either according to the binding,
or by itself if not bound:
\begin{code}
instantiateGVar :: Binding -> GenVar -> FreeVars
instantiateGVar bind (StdVar v)   =  instantiateVar    bind v
instantiateGVar bind (LstVar lv)  =  instantiateLstVar bind lv
\end{code}

\begin{eqnarray*}
   \beta(v) &=& v, \qquad  v \notin \beta
\\ \beta(v) &=& \beta.v, \qquad \mbox{if $\beta.v$ is a variable}
\\ \beta(v) &=& \fv(\beta.v), \quad \mbox{if $\beta.v$ is a term}
\end{eqnarray*}
\begin{code}
instantiateVar :: Binding -> Variable -> FreeVars
instantiateVar bind v
  = case lookupVarBind bind v of
        Nothing            ->  (S.singleton $ StdVar v,[])
        Just (BindVar v')  ->  (S.singleton $ StdVar v',[])
        Just (BindTerm t)  ->  freeVars t
\end{code}

\begin{eqnarray*}
   \beta(\lst v) &=& \setof{\lst v}, \qquad\qquad \lst v \notin \beta
\\ \beta(\lst v) &=& \elems(\beta.\lst v),
    \qquad\qquad \mbox{if $\beta.\lst v$ is a list}
\\ \beta(\lst v) &=& \beta.\lst v,
      \qquad\qquad \mbox{if $\beta.\lst v$ is a set}
\\ \beta(\lst v) &=& L \cup \bigcup \fv^*(T)
     \quad \mbox{if $\beta.\lst v$ has form $(L,T)$}
\end{eqnarray*}
\begin{code}
instantiateLstVar :: Binding -> ListVar -> FreeVars
instantiateLstVar bind lv
  = case lookupLstBind bind lv of
      Nothing             ->  (S.singleton $ LstVar lv, [])
      Just (BindList vl)  ->  (S.fromList vl, [])
      Just (BindSet  vs)  ->  (vs, [])
      Just (BindTLVs tlvs)
       -> let (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
          in  mrgFreeVarList
               (( S.fromList $ map LstVar lvs,[]) : map freeVars ts)
\end{code}
