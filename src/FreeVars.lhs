\section{Free Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( termFree
) where
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Variables
import AST

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

\subsection{Introduction}

Return the free variables of a term
---
pure and simple!

\begin{eqnarray*}
   fv(\kk k)  &\defs&  \emptyset
\\ fv(\vv v)  &\defs&  \{\vv v\}
\\ fv(\cc n {ts}) &\defs& \bigcup_{t \in ts} fv(ts)
\\ fv(\bb n {v^+} t) &\defs& fv(t)\setminus{v^+}
\\ fv(\ll n {v^+} t) &\defs& fv(t)\setminus{v^+}
\\ fv(\ss t {v^n} {t^n}) &\defs& (fv(t)\setminus{v^m})\cup \bigcup_{s \in t^m}fv(s)
\\ \textbf{where} && v^m = v^n \cap fv(t), t^m \textrm{ corr. to } v^m
\\ fv(\ii \bigoplus n {lvs}) &\defs& lvs
\end{eqnarray*}

\begin{code}
termFree :: Term -> VarSet
termFree (Var tk v)           =  S.singleton $ StdVar v
termFree (Cons tk n ts)       =  S.unions $ map termFree ts
termFree (Bind tk n vs tm)    =  termFree tm S.\\ vs
termFree (Lam tk n vl tm)     =  termFree tm S.\\ S.fromList vl
termFree (Sub tk tm s)        =  (tfv S.\\ tgtvs) `S.union` rplvs
   where
     tfv            =  termFree tm
     (tgtvs,rplvs)  =  substFree tfv s
termFree (Iter tk na ni lvs)  =  S.fromList $ map LstVar lvs
termFree _ = S.empty
\end{code}

\begin{code}
substFree tfv (Substn ts lvs) = (tgtvs,rplvs)
 where
   tl = S.toList ts
   lvl = S.toList lvs
   tgtvs = S.map (StdVar . fst) ts `S.union` S.map (LstVar . fst) lvs
   rplvs = S.empty `S.union` S.empty
\end{code}
