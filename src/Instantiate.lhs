\section{Instantiate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Instantiate
( InsContext, mkInsCtxt
, instantiate
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

\subsubsection{Instantiation Contexts}

All instantiations need a context argument that describes the following
aspects of the current state of a proof:
\begin{itemize}
  \item dynamic \texttt{Subscript}s in scope
\end{itemize}
\begin{code}
data InsContext
  =  ICtxt  { icSS :: [Subscript]
            }

mkInsCtxt = ICtxt
\end{code}


\newpage
\subsection{Instantiating Term with a (Total) Binding}

Here we require every free variable in the term to be also in the binding.
\begin{code}
instantiate :: MonadFail m => InsContext -> Binding -> Term -> m Term
\end{code}

\begin{eqnarray*}
   \beta.\kk k &=& \kk k
\\ \beta.\tt \tau &=& \tt \tau
\end{eqnarray*}
\begin{code}
instantiate _ binding v@(Val _ _)  =  return v
instantiate _ binding t@(Typ _)    =  return t
\end{code}

\begin{eqnarray*}
   \beta.(\vv v) &=& \beta(v)
\end{eqnarray*}
\begin{code}
instantiate insctxt binding vt@(Var tk v)
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
instantiate insctxt binding (Cons tk sb n ts)
  = fmap (Cons tk sb n) $ sequence $ map (instantiate insctxt binding) ts
\end{code}

\begin{eqnarray*}
   \beta.(\bb n {v^+} t) &=& \bb n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ll n {v^+} t) &=& \ll n {\beta^*.v^+} {\beta.t}
\end{eqnarray*}
\begin{code}
instantiate insctxt binding (Bnd tk n vs tm)
  = do vs' <- fmap theFreeVars $ instVarSet insctxt binding vs
       tm' <- instantiate insctxt binding tm
       bnd tk n vs' tm'
instantiate insctxt binding (Lam tk n vl tm)
  = do vl' <- instVarList insctxt binding vl
       tm' <- instantiate insctxt binding tm
       lam tk n vl' tm'
\end{code}

\begin{eqnarray*}
   \beta.(\xx n t) &=& \xx {n} {\beta.t}
\end{eqnarray*}
\begin{code}
instantiate insctxt binding (Cls n tm)
  = do tm' <- instantiate insctxt binding tm
       return $ Cls n tm'
\end{code}

We need to keep in mind that we use the substitution form to represent assignment. It the term is a predicate variable ``$:=$'',
then we have an assignment.
\begin{eqnarray*}
   \beta.(\ss {(:=)} {v^n} {t^n}) &=& \ss {(:=)} {\beta^*(v^n)} {\beta^*.t^n}
\\ \beta.(\ss t {v^n} {t^n}) &=& \ss {\beta.t} {\beta^*(v^n)} {\beta^*.t^n}
\end{eqnarray*}
\begin{code}
instantiate insctxt binding (Sub tk tm s)
  = do s' <- instSub insctxt binding s
       tm' <- if isAssignment tm
              then return tm
              else instantiate insctxt binding tm
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
instantiate insctxt binding (Iter tk sa na si ni lvs)
  = do lvtss <- instIterLVS insctxt binding lvs
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
instIterLVS :: MonadFail m => InsContext
            -> Binding -> [ListVar] -> m [[LVarOrTerm]]
instIterLVS insctxt binding lvs
  = do lvtss <- sequence $ map (instTLGVar insctxt binding) lvs
       let lvtss' = transpose lvtss
       checkAndGroup arity [] lvtss'
       -- fail "instIterLVS NYI"
  where
    arity = length lvs
\end{code}

\begin{code}
instTLGVar :: MonadFail m => InsContext -> Binding -> ListVar -> m [LVarOrTerm]
instTLGVar insctxt binding lv
  = case lookupLstBind binding lv of
      Nothing              ->  return $ [injLV lv]  -- maps to self !
      Just (BindList vl')  ->  return $ map injGV vl'
      Just (BindTLVs tlvs) ->  return tlvs
      _ -> fail "instTLGVar: bound to sets."

injV :: Variable -> LVarOrTerm
injV = injTM . varAsTerm
injGV :: GenVar -> LVarOrTerm
injGV (StdVar v)   =  injV v
injGV (LstVar lv)  =  injLV lv
\end{code}

\begin{code}
checkAndGroup :: MonadFail m => Int -> [[LVarOrTerm]] -> [[LVarOrTerm]]
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

The \texttt{Substn} constructor is used to represent substitutions,
and assignments.
\textbf{This requires separate treatment for the two cases.}

For both,
we expect the substitution target and replacement list-variables
to be bound to variable-lists, and not sets.

For substitution,
these lists should themselves only contain list-variables,
and for any target/replacement pair these lists will be of the same length.

For assignment,
these lists can contain general variables,
and arbitrary (expression) terms.
However the assignment only the second list-var to list-var component
of a substitution.

\begin{code}
instSub :: MonadFail m => InsContext -> Binding -> Substn -> m Substn
instSub insctxt binding (Substn ts lvs)
  = do ts'  <- instZip (instStdVar insctxt binding)
                       (instantiate insctxt binding) (S.toList ts)
       ts'' <- sequence $ map getTheTargetVar ts'
       vtlvss' <- instZip (instLLVar insctxt binding) (instLLVar insctxt binding)
                          (S.toList lvs)
       let (lvtlvss,rvtlvss) = unzip vtlvss'
       let (vtts,lvts) = unzip lvtlvss
       let (vtrs,lvrs) = unzip rvtlvss
       let lvs' = zip (concat lvts) (concat lvrs)
       let ts''' = zip (concat vtts) (concat vtrs)
       ts4 <- sequence $ map getTheTermVar ts'''
       substn (ts''++ts4) lvs'

instZip inst1 inst2 pairs
  = sequence $ map (instPair inst1 inst2) pairs
  where
    instPair inst1 inst2 (thing1,thing2)
      = do thing1' <- inst1 thing1
           thing2' <- inst2 thing2
           return (thing1',thing2')

getTheTargetVar :: MonadFail m => (FreeVars,Term) -> m (Variable,Term)
getTheTargetVar (fvs,tm)
  = do v' <- getTheVar fvs
       return (v',tm)

getTheTermVar :: MonadFail m => (Term,Term) -> m (Variable,Term)
getTheTermVar (Var _ v,t)  = return (v,t)
getTheTermVar (bt,_)       = fail ("getTheTermVar: expected Var, not "++show bt)

getTheVar :: MonadFail m => FreeVars -> m Variable
getTheVar fvs@(vs,diffs)
  = case S.toList vs of
      [StdVar v] | null diffs  ->  return v
      _  -> fail ("getTheVar: expected a single variable, not "++show fvs)
\end{code}

This code is used for list-var in substitutions only.
\begin{code}
instLLVar :: MonadFail m => InsContext
          -> Binding -> ListVar -> m ([Term],[ListVar])
instLLVar insctxt binding lv
  = case lookupLstBind binding lv of
      Just (BindList vl')  ->  do lvs <- fromGVarToLVar vl'
                                  return ([],lvs)
      Just (BindSet  vs')  ->  do lvs <- fromGVarToLVar $ S.toList vs'
                                  return ([],lvs)
      Just (BindTLVs tlvs) ->  return (tmsOf tlvs, lvsOf tlvs)
      Nothing              ->  fail $ unlines
                                     [ "instLLVar: l-var not found"
                                     , "l-var = " ++ trLVar lv
                                     , "bind = " ++ trBinding binding
                                     ]

fromGVarToLVar :: MonadFail m => VarList -> m [ListVar]
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
instVarSet :: MonadFail m => InsContext -> Binding -> VarSet -> m FreeVars
instVarSet insctxt binding vs
  = do fvss <- sequence $ map (instGVar insctxt binding) $ S.toList vs
       return $ mrgFreeVarList fvss
\end{code}



For a general variable:
\begin{eqnarray*}
   \beta.v &=& \beta(v)
\\ \beta.T &=& \fv(\beta(T))
\\ \beta.\lst g &=& \beta(\lst g)
\end{eqnarray*}
\begin{code}
instGVar :: MonadFail m => InsContext -> Binding -> GenVar -> m FreeVars
instGVar insctxt binding (StdVar v)  = instStdVar insctxt binding v
instGVar insctxt binding (LstVar lv) = instLstVar insctxt binding lv
\end{code}

\begin{code}
instStdVar :: MonadFail m => InsContext -> Binding -> Variable -> m FreeVars
instStdVar insctxt binding v
  = case lookupVarBind binding v of
      Nothing             ->  return $ single v  -- maps to self !
      Just (BindVar v')   ->  return $ single v'
      Just (BindTerm t')  ->  return $ freeVars t'
      _  ->  fail "instStdVar: bound to identifier."
  where single v = (S.singleton (StdVar v),[])
\end{code}

\begin{code}
instLstVar :: MonadFail m => InsContext -> Binding -> ListVar -> m FreeVars
instLstVar insctxt binding lv
  = case lookupLstBind binding lv of
      Nothing              ->  return $ single lv  -- maps to self !
      Just (BindList vl')  ->  return (S.fromList vl',[])
      Just (BindSet  vs')  ->  return (vs',[])
      Just (BindTLVs tlvs)
        | all isVar ts  -> return ( S.fromList
                                    $ ( map (StdVar . theVar) ts)
                                        ++ (map LstVar lvs)
                                  , [] )
        | otherwise     ->  fail "instLstVar: bound to non-variable terms."
        where (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
  where
    single lv = (S.singleton (LstVar lv),[])
\end{code}



With $L$ a list of general variables
\begin{eqnarray*}
   \beta.L &=& \mathsf{concat}_{g \in L} \beta.g
\end{eqnarray*}
\begin{code}
instVarList :: MonadFail m => InsContext -> Binding -> VarList -> m VarList
instVarList insctxt binding vl
  = fmap concat $ sequence $ map (instLGVar insctxt binding) vl
\end{code}
We do not expect these to map to terms.
\begin{code}
instLGVar :: MonadFail m => InsContext -> Binding -> GenVar -> m VarList
instLGVar insctxt binding (StdVar v)
  =  do fvs' <- instStdVar insctxt binding v
        v' <- getTheVar fvs'
        return [StdVar v]
instLGVar insctxt binding gv@(LstVar lv)
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
instantiateSC :: MonadFail m => InsContext -> Binding -> SideCond -> m SideCond
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
instantiateSC insctxt bind (ascs,freshvs)
  = do ascss' <- sequence $ map (instantiateASC insctxt bind) ascs
       freshvs' <- instVarSet insctxt bind freshvs
       mkSideCond [] (concat ascss') $ theFreeVars freshvs'
\end{code}
We compute $\beta.C$/$\beta.D$ first, failing (for now), if it has terms,
and then we compute  $\fv(\beta(T))$.
\begin{code}
instantiateASC :: MonadFail m => InsContext
               -> Binding -> AtmSideCond -> m [AtmSideCond]
instantiateASC insctxt bind asc
  = do (vsCD,diffs) <- instVarSet insctxt bind $ ascVSet asc
       if null diffs
         then instASCVariant insctxt vsCD fvsT asc
         else fail "instantiateASC: explicit diffs in var-set not handled."
  where
     fvsT = instantiateGVar insctxt bind $ ascGVar asc
\end{code}
\textbf{
  The use of \texttt{ascVSet} is problematic --- loss of uniformity info.
}


\begin{code}
instASCVariant :: MonadFail m => InsContext
               -> VarSet -> FreeVars -> AtmSideCond -> m [AtmSideCond]
instASCVariant insctxt vsD fvT (Disjoint _ _ _)   =  instDisjoint insctxt vsD fvT
instASCVariant insctxt vsC fvT (CoveredBy _ _ _)  =  instCovers   insctxt vsC fvT
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
instDisjoint :: MonadFail m => InsContext -> VarSet -> FreeVars -> m [AtmSideCond]
instDisjoint insctxt vsD (fF,fLessBs)
  =  return (asc1 ++ concat asc2)
  where
    asc1 = map (f1 vsD) (S.toList fF)
    asc2 = map (f2 vsD) fLessBs
    f1 vsD gv = Disjoint NonU gv vsD
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
instCovers :: MonadFail m => InsContext -> VarSet -> FreeVars -> m [AtmSideCond]
instCovers insctxt vsC (fF,fLessBs)
  =  return (asc1 ++ concat asc2)
  where
    asc1 = map (f1 vsC) (S.toList fF)
    asc2 = map (f2 vsC) fLessBs
    f1 vsC gv = CoveredBy NonU gv vsC
    f2 vsC (vsF,vsB) = map (f1 (vsC `S.union` vsB)) (S.toList vsF)
\end{code}

\subsubsection{Side-condition Variable Instantiation}

Instantiate a (std./list)-variable either according to the binding,
or by itself if not bound:
\begin{code}
instantiateGVar :: InsContext -> Binding -> GenVar -> FreeVars
instantiateGVar insctxt bind (StdVar v)   =  instantiateVar    insctxt bind v
instantiateGVar insctxt bind (LstVar lv)  =  instantiateLstVar insctxt bind lv
\end{code}

\begin{eqnarray*}
   \beta(v) &=& v, \qquad  v \notin \beta
\\ \beta(v) &=& \beta.v, \qquad \mbox{if $\beta.v$ is a variable}
\\ \beta(v) &=& \fv(\beta.v), \quad \mbox{if $\beta.v$ is a term}
\end{eqnarray*}
\begin{code}
instantiateVar :: InsContext -> Binding -> Variable -> FreeVars
instantiateVar insctxt bind v
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
instantiateLstVar :: InsContext -> Binding -> ListVar -> FreeVars
instantiateLstVar insctxt bind lv
  = case lookupLstBind bind lv of
      Nothing             ->  (S.singleton $ LstVar lv, [])
      Just (BindList vl)  ->  (S.fromList vl, [])
      Just (BindSet  vs)  ->  (vs, [])
      Just (BindTLVs tlvs)
       -> let (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
          in  mrgFreeVarList
               (( S.fromList $ map LstVar lvs,[]) : map freeVars ts)
\end{code}
