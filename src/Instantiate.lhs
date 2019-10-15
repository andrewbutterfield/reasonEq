\section{Instantiate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Instantiate
( instantiate
, instantiateASC
, instantiateSC
) where
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import Variables
import AST
import SideCond
import Binding
import FreeVars
import TestRendering

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

\subsection{Introduction}

We take a pattern term and a binding
and produce a re-constructed candidate term.
An important feature of this instantiation process is that
any pattern variable that is not bound remains the same
---we do not require bindings to explicity state that a pattern variable
mapped to itself in the relevant candidate.
A consequence of this is that instantiation shouldn't ever fail.
\begin{code}
instantiate :: Monad m => Binding -> Term -> m Term

instantiate binding val@(Val _ _) = return val

instantiate binding vt@(Var tk v)
  = case lookupVarBind binding v of
      Nothing             ->  return vt -- maps to self !
      Just (BindVar v')   ->  var tk v'
      Just (BindTerm t')  ->  return t'

instantiate binding (Cons tk n ts)
  = fmap (Cons tk n) $ sequence $ map (instantiate binding) ts

instantiate binding (Bind tk n vs tm)
  = do vs' <- instVarSet binding vs
       tm' <- instantiate binding tm
       bind tk n vs' tm'

instantiate binding (Lam tk n vl tm)
  = do vl' <- instVarList binding vl
       tm' <- instantiate binding tm
       lam tk n vl' tm'

instantiate binding (Cls n tm)
  = do tm' <- instantiate binding tm
       return $ Cls n tm'

instantiate binding (Sub tk tm s)
  = do tm' <- instantiate binding tm
       s' <- instSub binding s
       return $ Sub tk tm' s'

instantiate binding (Iter tk na ni lvs)
  = fail "instantiate NYFI -- Iter"
\end{code}

\newpage
\begin{code}
instSub :: Monad m => Binding -> Substn -> m Substn
instSub binding (Substn ts lvs)
  = do ts'  <- instZip (instVar binding)  (instantiate binding) ts
       lvs' <- instZip (instLVar binding) (instLVar binding)    lvs
       substn (S.toList ts') (S.toList lvs')
\end{code}

\begin{code}
instZip inst1 inst2 pairs
  = fmap S.fromList $ sequence $ map (instPair inst1 inst2) $ S.toList pairs
  where
    instPair inst1 inst2 (thing1,thing2)
      = do thing1' <- inst1 thing1
           thing2' <- inst2 thing2
           return (thing1',thing2')
\end{code}

\begin{code}
instVarSet :: Monad m => Binding -> VarSet -> m VarSet
instVarSet binding vs
  = fmap S.unions $ sequence $ map (instSGVar binding) $ S.toList vs
\end{code}

\begin{code}
instVarList :: Monad m => Binding -> VarList -> m VarList
instVarList binding vl
  = fmap concat $ sequence $ map (instLGVar binding) vl
\end{code}

\begin{code}
instSGVar :: Monad m => Binding -> GenVar -> m VarSet
instSGVar binding (StdVar v)
  =  fmap (S.singleton . StdVar) $ instVar binding v
instSGVar binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return $ S.singleton gv  -- maps to self !
      Just (BindList vl')  ->  return $ S.fromList vl'
      Just ( BindSet vs')  ->  return vs'
      _ -> fail "instSGVar: bound to terms."
\end{code}

\begin{code}
instLGVar :: Monad m => Binding -> GenVar -> m VarList
instLGVar binding (StdVar v)
  =  fmap ((\x -> [x]) . StdVar) $ instVar binding v
instLGVar binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return [gv]  -- maps to self !
      Just (BindList vl')  ->  return vl'
      _ -> fail "instLGVar: bound to sets or terms."
\end{code}

\newpage

\begin{code}
instGVar :: Monad m => Binding -> GenVar -> m GenVar
instGVar binding (StdVar v)  = do iv <- instVar binding v
                                  return $ StdVar iv
instGVar binding (LstVar lv) = do ilv <- instLVar binding lv
                                  return $ LstVar ilv
\end{code}

\begin{code}
instLVar :: Monad m => Binding -> ListVar -> m ListVar
instLVar binding lv
  = case lookupLstBind binding lv of
      Nothing                       ->  return lv  -- maps to self !
      Just (BindList [LstVar lv'])  ->  return lv'
      Just (BindSet vs')            -> getTheLVar vs'
      _ -> fail "instLVar: not bound to singleton list."
  where
    getTheLVar vs
     | S.size vs == 1
        = case S.elemAt 0 vs of
           (LstVar lv)  -> return lv
           _ -> fail "instLVar: bound to standard variable"
     | otherwise  =  fail "instLVar: not bound to singleton set."
\end{code}

\begin{code}
instVar :: Monad m => Binding -> Variable -> m Variable
instVar binding v
  = case lookupVarBind binding v of
      Nothing             ->  return v  -- maps to self !
      Just (BindVar v')   ->  return v'
      _  ->  fail "instVar: bound to term."
\end{code}

\newpage
\subsection{Side-Condition Instantiation}

Doing it again, with side-conditions.
\begin{code}
instantiateSC :: Monad m => Binding -> SideCond -> m SideCond
instantiateSC bind ascs
  = do ascss' <- sequence $ map (instantiateASC bind) ascs
       mkSideCond $ concat ascss'
\end{code}

\begin{code}
instantiateASC :: Monad m => Binding -> AtmSideCond -> m [AtmSideCond]
\end{code}

\paragraph{Is a Pre-condition}~

\begin{code}
instantiateASC bind asc@(IsPre _)  =  instantiateASCvs bind S.empty asc
\end{code}

\paragraph{Has Variable-Set}~

\begin{code}
instantiateASC bind asc
  = case instVarSet bind $ fromJust $ ascVSet asc of
      But msgs -> fail $ unlines $ msgs
      Yes (vs') -> instantiateASCvs bind vs' asc
\end{code}

\paragraph{Has General Variable}~

\begin{code}
instantiateASCvs bind vs' asc
  = case ascGVar asc of
      StdVar v  -> instantiateASCvsv  bind vs' v  asc
      LstVar lv -> instantiateASCvslv bind vs' lv asc
\end{code}

\paragraph{Has Standard Variable}~

\begin{code}
instantiateASCvsv bind vs' v (Disjoint _ _)
  = instantiateDisjoint vs' $ instantiateVar bind v
instantiateASCvsv bind vs' v (Covers _ _)
  = instantiateCovers vs' $ instantiateVar bind v
instantiateASCvsv bind vs' v (IsPre _)
  = fail "instantiateASC IsPre NYI"
instantiateASCvsv bind vs' v (ExCover _ _)
  = fail "instantiateASC ExCover should not occur!"
instantiateASCvsv bind vs' v (Exact _ _)
  = instantiateExact vs' $ instantiateVar bind v
\end{code}

\paragraph{Has List-Variable}~

\begin{code}
instantiateASCvslv bind vs' lv (Disjoint _ _)
  = instantiateDisjoint vs' $ instantiateLstVar bind lv
instantiateASCvslv bind vs' lv (Covers _ _)
  = fail "instantiateASCvslv Covers NYI"
instantiateASCvslv bind vs' lv (Exact _ _)
  = instantiateDisjoint vs' $ instantiateLstVar bind lv
\end{code}
Next,
Dealing with each condition, now that everything is instantiated.
Assume below that
$\setof{x,y}$ are distinct identifiers for observation variables
and $\setof{S,T}$ are distinct identifiers for term-valued variables.

\subsubsection{Disjointedness}

\textbf{Wrong: trying to discharge the side-condition!}
\textit{
See examples below
}

\begin{eqnarray*}
  S \disj T_1 \cup T2 &=& S \disj T_1 \land S \disj T_2
\\ S_1 \cup S_2 \disj T &=& S_1 \disj T \land S_2 \disj T
\end{eqnarray*}

\begin{eqnarray*}
   \setof{x,S} \disj \setof{y,T} &?&
\\ \setof{x,S} \disj \setof{x,T} &&  \false
\\ \setof{x,S} \disj \setof{y,S} &\text{if}&  S=\emptyset
\\ \setof{x,S} \disj \setof{y,T}
   &\text{if}&
   S \disj \setof{y,T} ; T \disj \setof{x,S}
\\&=& y \notin S \land x \notin T \land S \disj T
\\ \setof{\lst x,S} \disj \setof{\lst x,T}
   &\text{if}&
   \lst x = \emptyset \land S \disj T
\\ \setof{x,\lst S} \disj \setof{y,\lst S} &\text{if}&  \lst S = \emptyset
\end{eqnarray*}
\begin{code}
instantiateDisjoint :: Monad m => VarSet -> VarSet -> m [AtmSideCond]
instantiateDisjoint dvs fvs
 | freeObs `disjoint` dvs = return $ map (mkD dvs) $ S.toList freeTVar
 | otherwise  =  fail $ unlines
                   [ "Obs. free-vars not disjoint"
                   , "dvs = " ++ trVSet dvs
                   , "fvs = " ++ trVSet fvs
                   ]
 where
   (freeObs,freeTVar) = S.partition isObsGVar fvs
   mkD vs gv = Disjoint gv vs
\end{code}

\newpage
\subsubsection{Covering}

\begin{eqnarray*}
   S \supseteq T_1 \cup T2 &=& S \supseteq T_1 \land S \supseteq T_2
\\ S_1 \cup S_2 \supseteq T &\neq& S_1 \supseteq T \land S_2 \supseteq T
\end{eqnarray*}


\begin{eqnarray*}
   \setof{x,S} \supseteq \setof{y,T} &?&
\\ \setof{x,S} \supseteq \setof{x,T} &\text{if}&  \setof{x,S} \supseteq T
\\ \setof{x,S} \supseteq \setof{y,S} &\text{if}&  y \in S
\\ \setof{x,S} \supseteq \setof{y,T}
   &\text{if}&
   y \in S \and \setof{x,S} \supseteq T
\\ \setof{\lst x,S} \supseteq \setof{\lst x,T}
   &\text{if}&
   \setof{\lst x,S} \supseteq T
\\ \setof{x,\lst S} \supseteq \setof{y,\lst S} &\text{if}& y \in \lst S
\end{eqnarray*}
\begin{code}
instantiateCovers :: Monad m => VarSet -> VarSet -> m [AtmSideCond]
instantiateCovers cvs fvs
 | freeObs `S.isSubsetOf` cvs = return $ map (mkC cvs) $ S.toList freeTVar
 | otherwise  =  fail $ unlines
                   [ "Obs. free-vars not covered"
                   , "cvs = " ++ trVSet cvs
                   , "fvs = " ++ trVSet fvs
                   ]
 where
   (freeObs,freeTVar) = S.partition isObsGVar fvs
   mkC vs gv = Covers gv vs
\end{code}


\subsubsection{Pre-Condition}

Not yet covered

\subsubsection{Exactness}


\begin{code}
instantiateExact :: Monad m => VarSet -> VarSet -> m [AtmSideCond]
instantiateExact cvs fvs
 | fvs == cvs = return $ map (mkX cvs) $ S.toList freeTV
 | otherwise  =  fail $ unlines
                   [ "free-vars not exact"
                   , "cvs = " ++ trVSet cvs
                   , "fvs = " ++ trVSet fvs
                   ]
 where
   freeTV = S.filter (not . isObsGVar) fvs
   mkX vs gv = Exact gv vs
\end{code}


\subsubsection{Side-condition Variable Instantiation}

Instantiate a (std./list)-variable either according to the binding,
or by itself if not bound:
\begin{code}
instantiateVar :: Binding -> Variable -> VarSet
instantiateVar bind v
  = case lookupVarBind bind v of
        Nothing            ->  S.singleton $ StdVar v
        Just (BindVar v)   ->  S.singleton $ StdVar v
        Just (BindTerm t)  ->  termFree t

instantiateLstVar :: Binding -> ListVar -> VarSet
instantiateLstVar bind lv
  = case lookupLstBind bind lv of
      Nothing                 ->  S.singleton $ LstVar lv
      Just (BindList vl)      ->  S.fromList vl
      Just (BindSet  vs)      ->  vs
      Just (BindTLVs ts lvs)  ->  (S.unions $ map termFree ts)
                                  `S.union`
                                  (S.fromList $ map LstVar lvs)
\end{code}
