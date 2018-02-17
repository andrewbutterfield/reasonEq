\section{Instantiate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Instantiate
( instantiate
) where
import Data.Set(Set)
import qualified Data.Set as S

import Variables
import AST
import Binding

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
\begin{code}
instantiate :: Monad m => Binding -> Term -> m Term

instantiate binding val@(Val _ _) = return val

instantiate binding vt@(Var tk v)
  = case lookupBind binding v of
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

instantiate binding (Sub tk tm s)
  = do tm' <- instantiate binding tm
       s' <- instSub binding s
       return $ Sub tk tm' s'

instantiate binding (Iter tk na ni lvs)
  = error "instantiate NYFI -- Iter"
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
  = case lookupBind binding v of
      Nothing             ->  return v  -- maps to self !
      Just (BindVar v')   ->  return v'
      _  ->  fail "instVar: bound to term."
\end{code}
