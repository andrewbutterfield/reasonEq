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

\subsection{Need for Variable-Set Expressions}

Consider the following extract from the standard free-variable definition:
\begin{eqnarray*}
   \fv &:& T \fun \Set{V}
\\  \fv(\vv v)  &\defs&  \{\vv v\}
\\ \fv(\bb n {v^+} t) &\defs& \fv(t)\setminus{v^+}
\end{eqnarray*}
In general we need to work with variable-set \emph{expressions}.
In particular we need to be able to note when predicate and expression
variables are subject to set removal because they are under a binding construct.

\newpage

We interpret the occurrence of a predicate or expression variable
in a variable-set
as symbolically denoting its putative free observational variables.

So $\setof{\vv x, \vv e, \vv P}$ actually denotes
$\setof{\vv x} \cup \fv(\vv e) \cup \fv(\vv P)$.

We need to be able to represent
$\setof{\vv x, \vv e, \vv P} \setminus B$,
where $B$ denotes a set of variable bindings.
In effect we have a small set expression language
that has explicit enumerations, symbolic variables,
with set union and difference.
Given the following two set laws,
\begin{eqnarray*}
   (F_1 \cup F_2) \setminus B      &=& (F_1\setminus B) \cup (F_2 \setminus B)
\\ (F \setminus B_1) \setminus B_2 &=& F \setminus (B_1 \cup B_2)
\end{eqnarray*}
\def\FVE{\textit{FVE}}
we can represent a free-variable set-expression (\FVE) as an enumeration,
paired with a collection of non-trivial set difference terms,
each a pair of enumerations.
\[
   \bigcup
   \left(
   \setof{\vv v\dots}
   ,
   \setof{(\setof{\vv v,\dots}\circleddash\setof{\vv v,\dots})
          ,\dots,
          (\setof{\vv v,\dots}\circleddash\setof{\vv v,\dots})}
   \right)
\]
Here we use $\circleddash$ to denote an intent to perform set subtraction.
The first enumerations in each pair
consist solely of predicate and expression variables.
Also, none of those variables appear in the corresponding second enumeration.

We need to consider how to tidy-up/``normalise'' these
structures.
For example:
\begin{eqnarray*}
  &&  \bigcup(F,\setof{\dots,(F_i\circleddash B_i),\dots})
\\&=& \bigcup(F,\setof{\dots,(F_i\circleddash B_i)\setminus F,\dots}),
      \qquad \because (F \cup A) = (F \cup (A \setminus F))
\\&=& \bigcup(F,\setof{\dots,(F_i\circleddash(B_i \cup F)),\dots})
\\&=& \bigcup(F,\setof{\dots,(F_i\setminus F)\circleddash B_i),\dots})
\end{eqnarray*}
Bascially, there is no need for any element in $F$ to appear in any $F_i$,
as its possible removal by $B_i$ has no effect
on its presence as a free variable.

\begin{code}
type FreeVars = (VarSet, [(VarSet,VarSet)])
\end{code}

A common case is where nothing is being subtracted:
\begin{eqnarray*}
   inj &:& \Set{V} \fun \FVE
\\ inj(F) &\defs& (F,\emptyset)
\end{eqnarray*}
\begin{code}
injVarSet :: VarSet -> FreeVars
injVarSet vs = (vs,[])
\end{code}


\newpage
Lets start with the simplest general case: $F \setminus B$ for arbitrary $F$ and $B$:

All possibilities are covered by this (2nd-order) example:
\begin{eqnarray*}
  & & \setof{\vv x, \vv y, \vv e, \vv f, \vv P, \vv Q}
      \setminus
      \setof{\vv x, \vv z, \vv e, \vv g, \vv P, \vv R}
\\&=& ( \setof{\vv y}
      ,
      \setof{( \setof{\vv f,\vv Q}
               \circleddash
               \setof{\vv x, \vv z, \vv g, \vv R} )})
\\&=& ( \setof{\vv y}
      ,
      \setof{( \setof{\vv f,\vv Q}
               \circleddash
               \setof{\vv x, \vv z} )})
      \qquad \because (F \setminus B) = (F \setminus (B \cap F)),
               \textrm{ and } \vv z \in \vv f, \vv Q \textrm{ is poss.}
\end{eqnarray*}
In the more common first-order setting we have:
\begin{eqnarray*}
  & & \setof{\vv x, \vv y, \vv e, \vv f, \vv P, \vv Q}
      \setminus
      \setof{\vv x, \vv z}
\\&=& ( \setof{\vv y}
      ,
      \setof{( \setof{\vv e, \vv f, \vv P, \vv Q}
               \circleddash
               \setof{\vv x, \vv z} )})
      \qquad \vv z \in \vv e, \vv f, \vv P, \vv Q\textrm{ is poss.}
\end{eqnarray*}

The treatment of the 2nd-order example is as follows:
\begin{eqnarray*}
  & & \setof{\vv x, \vv y, \vv e, \vv f, \vv P, \vv Q}
      \ominus
      \setof{\vv x, \vv z, \vv e, \vv g, \vv P, \vv R}
\\&=& (\setof{\vv x, \vv y} \cup \setof{\vv e, \vv f, \vv P, \vv Q})
      \ominus
      (\setof{\vv x, \vv z} \cup \setof{\vv e, \vv g, \vv P, \vv R})
\\&=& ( \setof{\vv x, \vv y} \ominus \setof{\vv x, \vv z} )
      \cup
      ( \setof{\vv e, \vv f, \vv P, \vv Q}
        \ominus
        \setof{\vv e, \vv g, \vv P, \vv R} )
\\&\mapsto&
      ( \setof{\vv y}, \emptyset )
      \oplus
      ( \setof{\vv f, \vv Q}
      ,
      \setof{\vv x, \vv z} )
\\&=& ( \setof{\vv y}
      , \setof{( \setof{\vv f, \vv Q}\circleddash \setof{\vv x, \vv z} )} )
\end{eqnarray*}
Here we use $\oplus$ to denote a binary operator that returns the ``union''
of two free-variable sets (details to follow).

In a general setting,
where $X$ denotes sets of observational variables,
and $T$ denotes sets of predicate and expression variables,
we have:
\begin{eqnarray*}
  & & (X_F \sqcup T_F) \ominus (X_B \sqcup T_F)
\\&=& ( X_F \ominus X_B ) \cup ( T_F \ominus T_B )
\\&\mapsto&
      ( (X_F \setminus X_B), \emptyset ) \oplus (( T_F \setminus T_B ) , X_B )
\\&=& ( (X_F \setminus X_B)
      , \setof{ ( ( T_F \setminus T_B ) \circleddash X_B ) } )
\\&=& ( X_F  \cup ( T_F \setminus T_B ), \emptyset),
      \qquad  X_B = \emptyset
\\&=& ( X_F,  \emptyset),
      \qquad\qquad\qquad\quad  ( T_F \setminus T_B ) = \emptyset
\end{eqnarray*}

We can implement this without explicitly using $\oplus$:
\begin{eqnarray*}
   \_\ominus\_ &:& \Set{V} \times \Set{V} \fun \FVE
\\ (X_F \sqcup T_F) \ominus (X_B \sqcup T_B)
   &\defs& opt( (X_F \setminus X_B)
              , ( T_F \setminus T_B ) \circleddash X_B ) )
\\ opt(V,(F \circleddash B))
   &\defs&
   \left\{
   \begin{array}{ll}
      (V \cup F, \emptyset),     & B = \emptyset
   \\ (V, \emptyset),            & F = \emptyset
   \\ (V, \setof{(F \circleddash B)}), & \textrm{otherwise}
   \end{array}
   \right.
\end{eqnarray*}
\begin{code}
genFreeVars :: VarSet -> VarSet -> FreeVars
genFreeVars fvs bvs
  | S.null xb  =  (xd `S.union` td, [])
  | S.null td  =  (xd, [])
  | otherwise  =  (xd,[(td,xb)])
  where
    (xb,tb) = S.partition isObsGVar bvs
    (xf,tf) = S.partition isObsGVar fvs
    xd = xf S.\\ xb
    td = tf S.\\ tb
\end{code}

\newpage

We will need a way to merge these ``sets'' ($\oplus$),
and a way to subtract from them ($sub$).
\begin{eqnarray*}
   \_\oplus\_ &:& \FVE \times \FVE \fun \FVE
\\ (F_1,D_1) \oplus (F_2,D_2)
   &\defs&
   (F_1 \cup F_2, rem_{F_2}(D_1) \cup rem_{F_1}(D_2)
\end{eqnarray*}
\begin{code}
mrgFreeVars :: FreeVars -> FreeVars -> FreeVars
mrgFreeVars (fvs1,diffs1) (fvs2,diffs2)
  =( fvs1 `S.union` fvs2
   , map (remVarSet fvs2) diffs1 ++ map (remVarSet fvs1) diffs2 )
\end{code}
\begin{eqnarray*}
   rem_{F'} \setof{F\circleddash B} &\defs& \setof{(F\setminus F')\circleddash B}
\end{eqnarray*}
\begin{code}
remVarSet :: VarSet -> (VarSet,VarSet) -> (VarSet,VarSet)
remVarSet vs (fvs,bvs) = (fvs S.\\ vs, bvs)
\end{code}


\begin{eqnarray*}
   sub &:& \FVE \times \Set{V} \fun \FVE
\\ (F,\setof{D_i}) \setminus S
   &=&
   (F \ominus S)
   \oplus
   (\emptyset, \setof{D_i \oslash S})
\end{eqnarray*}
\begin{code}
subVarSet :: FreeVars -> VarSet -> FreeVars
subVarSet (fvs, diffs) vs
 =  mrgFreeVars (genFreeVars fvs vs) (S.empty,map (subMore vs) diffs)
\end{code}

\begin{eqnarray*}
   \_\oslash\_
   &:&
   (\Set{V}\times\Set{V}) \times \Set{V} \fun \Set{V}\times\Set{V}
\\ (F\circleddash B) \oslash S &\defs& (F \circleddash (B \cup S))
\end{eqnarray*}
\begin{code}
-- we flip arguments to facilitate mapping
subMore :: VarSet -> (VarSet,VarSet) -> (VarSet,VarSet)
subMore vs (fvs,bvs)  =  (fvs,bvs `S.union` vs)
\end{code}


\newpage

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
freeVars (Cons tk sb n ts)    =  S.unions $ map freeVars ts
freeVars (Bnd tk n vs tm)     =  freeVars tm S.\\ vs
freeVars (Lam tk n vl tm)     =  freeVars tm S.\\ S.fromList vl
freeVars (Cls _ _)            =  S.empty
freeVars (Sub tk tm s)        =  (tfv S.\\ tgtvs) `S.union` rplvs
   where
     tfv            =  freeVars tm
     (tgtvs,rplvs)  =  substRelFree tfv s
freeVars (Iter tk sa na si ni lvs)  =  S.fromList $ map LstVar lvs
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
zeroTermIdNumbers (Cons tk sb n ts) = Cons tk sb n $ map zeroTermIdNumbers ts
zeroTermIdNumbers (Bnd tk n vs tm) = fromJust $ bnd tk n (zeroVSetIdNumbers vs)
                                              $ zeroTermIdNumbers tm
zeroTermIdNumbers (Lam tk n vl tm) = fromJust $ lam tk n (zeroVListIdNumbers vl)
                                              $ zeroTermIdNumbers tm
zeroTermIdNumbers (Cls n tm)  = Cls n $ zeroTermIdNumbers tm
zeroTermIdNumbers (Sub tk tm s) = Sub tk (zeroTermIdNumbers tm)
                                      $ zeroSubIdNumbers s
zeroTermIdNumbers (Iter tk sa na si ni lvs)
  = Iter tk sa na si ni $ map zeroLVarIdNumber lvs
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
