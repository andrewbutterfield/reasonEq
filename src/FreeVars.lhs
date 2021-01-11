\section{Free Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019--2021

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( freeVars
, substRelFree
, zeroTermIdNumbers
, setVarIdNumber
, nestSimplify
-- exports for test only
, int_tst_FreeVar
) where

import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List
import Data.Maybe

import Utilities (injMap)
import Control (mapboth,mapaccum,mapsnd)
import LexBase
import Variables
import AST
import SideCond

import Test.HUnit ((@?=))
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

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
     (tgtvs,rplvs)  =  substRelFree tfv s
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
This function returns the free variables in a substitution
\emph{relative} to a given term to which it is being applied.
It also returns the free variables from that term that will be substituted for.
\begin{code}
substRelFree :: VarSet -> Substn -> (VarSet,VarSet)
substRelFree tfv (Substn ts lvs) = (tgtvs,rplvs)
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

Support for quantifier nesting needs to be hardwired in.

\subsubsection{Zeroing a term}

It can help to put a term into a state where all identifiers have zero
as their unique number
---
this could prevent the emergence of large numbers during a long proof.
\begin{code}
zeroTermIdNumbers :: Term -> Term
zeroTermIdNumbers (Var tk v) = fromJust $ var tk $ zeroVarIdNumber v
zeroTermIdNumbers (Cons tk n ts) = Cons tk n $ map zeroTermIdNumbers ts
zeroTermIdNumbers (Bnd tk n vs tm) = fromJust $ bnd tk n (zeroVSetIdNumbers vs)
                                              $ zeroTermIdNumbers tm
zeroTermIdNumbers (Lam tk n vl tm) = fromJust $ lam tk n (zeroVListIdNumbers vl)
                                              $ zeroTermIdNumbers tm
zeroTermIdNumbers (Cls n tm)  = Cls n $ zeroTermIdNumbers tm
zeroTermIdNumbers (Sub tk tm s) = Sub tk (zeroTermIdNumbers tm)
                                      $ zeroSubIdNumbers s
zeroTermIdNumbers (Iter tk na ni lvs) = Iter tk na ni $ map zeroLVarIdNumber lvs
zeroTermIdNumbers trm = trm
\end{code}

Drilling down \dots
\begin{code}
zeroSubIdNumbers :: Substn -> Substn
zeroSubIdNumbers (Substn ts lvs) = fromJust $ substn ts0 lvs0
 where ts0 =  map zeroTrmSbIdNumbers $ S.toList ts
       lvs0 = map zeroLVLVIdNumbers  $ S.toList lvs

zeroTrmSbIdNumbers :: (Variable,Term) -> (Variable,Term)
zeroTrmSbIdNumbers (v,t) = (zeroVarIdNumber v, zeroTermIdNumbers t)

zeroLVLVIdNumbers :: (ListVar,ListVar) -> (ListVar,ListVar)
zeroLVLVIdNumbers (lv1,lv2) = (zeroLVarIdNumber lv1, zeroLVarIdNumber lv2)

zeroVListIdNumbers :: VarList -> VarList
zeroVListIdNumbers vl = map zeroGVarIdNumber vl

zeroVSetIdNumbers :: VarSet -> VarSet
zeroVSetIdNumbers vs = S.map zeroGVarIdNumber vs

zeroGVarIdNumber :: GenVar -> GenVar
zeroGVarIdNumber (StdVar v) = StdVar $ zeroVarIdNumber v
zeroGVarIdNumber (LstVar lv) = LstVar $ zeroLVarIdNumber lv

zeroLVarIdNumber (LVbl v is js) = LVbl (zeroVarIdNumber v) is js

zeroVarIdNumber :: Variable -> Variable
zeroVarIdNumber (Vbl idnt cls whn) = Vbl (zeroIdNumber idnt) cls whn

zeroIdNumber :: Identifier -> Identifier
zeroIdNumber (Identifier nm _) = fromJust $ uident nm 0

setVarIdNumber :: Int -> Variable -> Variable
setVarIdNumber u (Vbl (Identifier nm _) cls whn)
  = Vbl (fromJust $ uident nm u) cls whn
\end{code}

\newpage


\newpage

\subsubsection{Nesting Simplification}

So we have to hardwire the basic simplification laws:
\begin{eqnarray*}
   (\bb n {V_i }{\bb n {V_j} P})
   &=& (\bb n {(V_i \cup V_j)}  P)
\\ (\bb i {V_i} {\bb j {V_j} P)}
   &=& (\bb i {(V_i\setminus V_j)} {\bb j {V_j}  P})
\\ &=& \bb j {V_j}  P, \qquad \IF ~V_i \subseteq V_j
\\ (\ll n {\sigma_i } {\ll n {\sigma_j \cat \sigma_k} P})
   &=& (\ll n {(\sigma_i \cat \sigma_j)}  {\ll n {\sigma_k} P}),
       \qquad \elems \sigma_i \disj \elems \sigma_j
\end{eqnarray*}

\textbf{This code may be rendered obsolete by the addition of unique numbers
to Identifiers along with quantifier normalisation
}

Function \texttt{nestSimplify} returns a simplified term
if one of the laws above applies, otherwise it fails.
\begin{code}
nestSimplify :: Monad m => Term -> m Term

nestSimplify (Bnd tk1 n1 vs1 t1@(Bnd tk2 n2 vs2 t2))
 | tk1 /= tk2              =  fail ("nestSimplify: mixed bind term-kinds")
 | n1 /= n2                =  bnd tk1 n1 (vs1 S.\\ vs2) t1
 | vs1 `S.isSubsetOf` vs2  =  return t1
 | otherwise               =  bnd tk1 n1 (vs1 `S.union` vs2) t1

nestSimplify (Lam tk1 n1 vl1 (Lam tk2 n2 vl2 t2))
 | tk1 /= tk2  =  fail ("nestSimplify: mixed lambda term-kinds")
 | n1  == n2   =  lam tk1 n1 (vl1 ++ vl2) t2
 | otherwise   =  fail ("nestSimplify: mixed lambda forms")

nestSimplify trm = fail "nestSimplify: not nested similar quantifiers"
\end{code}

\textbf{NOT VERY SATISFACTORY IN THE \texttt{[]\_idem} PROOF}

\textsf{
We need something that simplifies $\bb i {V_i }{\bb j {V_j} P}$
to $\bb j {V_j} P$, because $V_j \supseteq \fv(P)$.
}

\newpage

\subsection{Tests}

\begin{code}

tst_setVarIdNumber :: TF.Test

va = Vbl (jId "a") ObsV Before
a0 = Vbl (jIdU "a" 0) ObsV Before
a1 = Vbl (jIdU "a" 1) ObsV Before

tst_setVarIdNumber
 = testGroup "setVarIdNumber"
     [ testCase "a is a.0" ( va  @?= a0 )
     , testCase "set a .0" ( setVarIdNumber 0 va  @?= a0 )
     , testCase "set a .1" ( setVarIdNumber 1 va  @?= a1 )
     ]
\end{code}

\begin{code}
int_tst_FreeVar :: [TF.Test]
int_tst_FreeVar
  = [ testGroup "\nFreeVar (INTERNAL)"
      [ tst_setVarIdNumber
      ]
    ]
\end{code}
