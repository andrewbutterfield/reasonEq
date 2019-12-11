\section{Free Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( freeVars
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
and then continue by addressing nested quantifiers.


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
freeVars (Bnd tk n vs tm)     =  freeVars tm S.\\ vs
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
\subsection{Quantifier Nesting}

We cannot write laws to simplify nested quantifiers
because we want to condition laws to have no shadowing of bound variables.
So we have to hardwire the basic simplication law:
\[
       (\Gamma_i V_i \bullet \Gamma_j V_j \bullet P)
       =
       (\Gamma_i (V_i\setminus V_j) \bullet \Gamma_j V_j \bullet P)
\]
Only applicable when variable-sets are used in a quantifier.
