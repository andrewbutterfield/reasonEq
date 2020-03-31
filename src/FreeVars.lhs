\section{Free Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( freeVars
, substRelFree
, zeroTermIdNumbers
, normaliseQuantifiers
, setVarIdNumber
, nestSimplify
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

import Test.HUnit
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
\end{code}

\newpage

\subsubsection{Normalising Bound Variables}

We want all bound-variables to be unique in a term, so that, for example,
the term
$$
  \forall x \bullet x > y \land \exists x \bullet x = z + 42
  \qquad
  (\text{really:  }
   \forall x_0 \bullet x_0 > y_0 \land \exists x_0 \bullet x_0 = z_0 + 42)
$$
becomes:
$
  \forall x_i \bullet x_i > y_0 \land \exists x_j \bullet x_j = z_0 + 42
$
where $i > 0$, $j > 0$, and $i \neq j$.

Turns out there is a fairly simple algorithm, that doesn't require the
predicate to be zero'ed in advance!
\begin{eqnarray*}
   \theta,\mu : VV &\defs&  name \pfun \Nat
\\
\\ Norm &:& T \fun T
\\ Norm(P)                       &\defs& \pi_1(norm_\theta(P))
\\
\\ norm &:& VV \fun T \fun (T \times VV)
\\ norm_\mu(v)         &\defs & (v_{\mu(v)} \cond{v \in \mu} v_0,\mu)
\\ norm_\mu(P \land Q) &\defs & (P' \land Q',\mu'')
\\                     &\where& (P',\mu') = norm_\mu(P)
\\                     &      & (Q',\mu'') = norm_{\mu'}(Q)
\\ norm_\mu(\forall x \bullet P) &\defs& (\forall x_{\mu'(x)} \bullet P',\mu'')
\\                     &\where& \mu' = (\mu\override\maplet x 1)
                                       \cond{x \in \mu}
                                       (\mu\override\maplet x {\mu(x)+1})
\\                     &      & (P',\mu'') = norm_{\mu'}(P)
\end{eqnarray*}
Note that we need to thread the map parameter $\mu$ into and out of each call
to $norm$ to ensure that we get full uniqueness of bound variable numbers.

We map bound variable names to their unique numbers:
\begin{code}
type VarVersions = Map String Int
\end{code}

Quantifier normalisation:
\begin{code}
normaliseQuantifiers :: Term -> Term
normaliseQuantifiers = fst . normQ M.empty
\end{code}

The real work is done here:
\begin{code}
normQ :: VarVersions -> Term -> (Term, VarVersions)
\end{code}



\begin{eqnarray*}
   norm_\mu(v)         &\defs & (v_{\mu(v)} \cond{v \in \mu} v_0,\mu)
\end{eqnarray*}
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv (Var tk v@(Vbl (Identifier nm _) _ _))
     =  (fromJust $ var tk $ normQVar vv v, vv)
\end{code}


\newpage


\begin{eqnarray*}
   norm_\mu(P \land Q) &\defs & (P' \land Q',\mu'')
\\                     &\where& (P',\mu') = norm_\mu(P)
\\                     &      & (Q',\mu'') = norm_{\mu'}(Q)
\end{eqnarray*}
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv (Cons tk n ts)       =  (Cons tk n ts',vv')
                              where (ts',vv') =  mapaccum normQ vv ts
normQ vv (Cls n tm)           =  (Cls n tm',vv')
                              where (tm',vv') =  normQ vv tm
normQ vv (Sub tk tm s)
  = let (tm',vv') = normQ vv tm
        (s',vv'') = normQSub vv' s
    in (Sub tk tm' s',vv'')

normQ vv (Iter tk na ni lvs)  =  (Iter tk na ni $ map (normQLVar vv) lvs,vv)
\end{code}





\begin{eqnarray*}
   norm_\mu(\forall x \bullet P) &\defs& (\forall x_{\mu'(x)} \bullet P',\mu'')
\\                     &\where& \mu' = (\mu\override\maplet x 1)
                                       \cond{x \in \mu}
                                       (\mu\override\maplet x {\mu(x)+1})
\\                     &      & (P',\mu'') = norm_{\mu'}(P)
\end{eqnarray*}
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv (Bnd tk n vs tm)
 = let (vl',vv') = normQBound vv $ S.toList vs
       (tm',vv'') =  normQ vv' tm
   in ( fromJust $ bnd tk n (S.fromList vl') tm', vv')
normQ vv (Lam tk n vl tm)
 = let (vl',vv') = normQBound vv vl
       (tm',vv'') =  normQ vv' tm
   in ( fromJust $ lam tk n vl' tm', vv')
\end{code}





Anything else is unchanged
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv trm = (trm, vv) -- Val, Typ
\end{code}

\newpage

Functions that modify \texttt{VarVersions} \dots
\begin{code}
normQSub vv (Substn ts lvs)
  = let lvl' = mapboth (normQLVar vv) $ S.toList lvs
        (tl',vv') = normQTermSub vv $ S.toList ts
    in (fromJust $ substn tl' lvl', vv')

normQTermSub vv tl = mapaccum normQVarTerm vv tl

normQVarTerm vv (v,tm)
  = ((normQVar vv v, tm'), vv')
  where (tm',vv') = normQ vv tm

-- (vl',vv') = normQBound vv vl
normQBound vv [] = ([],vv)
normQBound vv (gv:gvs)
  = let (gv',vv') = normQBGVar vv gv
        (gvs',vv'') = normQBound vv' gvs
    in (gv':gvs', vv'')

normQBGVar vv (LstVar lv)
  =  let  (lv',vv') = normQBLVar vv lv  in  (LstVar lv', vv')
normQBGVar vv (StdVar v)
  =  let  (v', vv') = normQBVar  vv  v  in  (StdVar v',  vv')

normQBLVar vv (LVbl v is js)
  = let  (v',vv') = normQBVar vv v  in  (LVbl v' is js, vv')

normQBVar vv v@(Vbl (Identifier nm _) _ _)
 = case M.lookup nm vv of
     Nothing ->  (setVarIdNumber 1 v, M.insert nm 1 vv)
\end{code}



Functions that lookup \texttt{VarVersions}\dots
\begin{code}
normQLVar vv (LVbl v is js) = LVbl (normQVar vv v) is js

normQVar vv v@(Vbl (Identifier nm _) _ _)
 = setVarIdNumber (M.findWithDefault 0 nm vv) v

setVarIdNumber :: Int -> Variable -> Variable
setVarIdNumber u (Vbl (Identifier nm _) cls whn)
  = Vbl (fromJust $ uident nm u) cls whn
\end{code}

\newpage

\subsubsection{Nesting Simplification}

So we have to hardwire the basic simplification laws:
\begin{eqnarray*}
   (\bb n {V_i }{\bb n {V_j} P})
   &=& (\bb n {(V_i \cup V_j)}  P)
\\ (\bb i {V_i} {\bb j {V_j} P)}
   &=& (\bb i {(V_i\setminus V_j)} {\bb j {V_j}  P})
\\ &=& \bb j {V_j}  P, \qquad \IF ~V_i \subseteq V_j
\\ (\ll n {\sigma_i } {\ll n {\sigma_j} P})
   &=& (\ll n {(\sigma_i \cat \sigma_j)}  P)
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

jId = fromJust . ident
jIdU nm u = fromJust $ uident nm u
identi nm i = jId (nm++show i) -- number is part of name

va = Vbl (jId "a") ObsV Before
a0 = Vbl (jIdU "a" 0) ObsV Before
a1 = Vbl (jIdU "a" 1) ObsV Before

tst_setVarIdNumber
 = testGroup "setVarIdNumber"
     [ testCase "a is a.0"
       ( va  @?= a0 )
     , testCase "set a .0"
       ( setVarIdNumber 0 va  @?= a0 )
     , testCase "set a .1"
       ( setVarIdNumber 1 va  @?= a1 )
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
