\chapter{Free Variables}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2019--2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module FreeVars
( FreeVars
, noFreevars, injVarSet
, freeVars
, inFreeVars, theFreeVars
, mrgFreeVars, mrgFreeVarList
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

import Debugger
\end{code}

\section{Introduction}

The definition of the free variables of a term/formula in logic
is usually quite straighforward.
However, we complicate matters by having: 
variables that denote terms;
explicit substitutions;
and list-variables.

\subsection{Need for Variable-Set Expressions}

Consider the following extract from the standard free-variable definition:
\begin{eqnarray*}
   \fv &:& T \fun \Set{V}
\\ \fv(\vv v)  &\defs&  \{\vv v\}
\\ \fv(\bb n {v^+} t) &\defs& \fv(t)\setminus{v^+}
\end{eqnarray*}
In general we need to work with variable-set \emph{expressions}.
In particular we need to be able to note when predicate and expression
variables are subject to set removal because they are under a binding construct.

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
Consider the following two set laws:
\begin{eqnarray*}
   (F_1 \cup F_2) \setminus B      &=& (F_1\setminus B) \cup (F_2 \setminus B)
\\ (F \setminus B_1) \setminus B_2 &=& F \setminus (B_1 \cup B_2)
\end{eqnarray*}
The first law allows us to breakdown $F\setminus B$, 
with $ F = \setof{v_1,\dots,v_n}$,
into the form $\setof{v_1}\setminus B \cup \dots \cup \setof{v_n}\setminus B$.
The second allows us to group together 
all the $B_i$ associated with any given $F$.
\def\FVE{\textit{FVE}}
This means that we can represent a free-variable set-expression (\FVE) 
as an enumeration,
paired with a collection of non-trivial set difference terms,
each a pair of enumerations, the first element of which is a singleton:
\[
   \bigcup
   \left(
   \setof{\vv v\dots}
   ,
   \setof{(\vv v \circleddash\setof{\vv v,\dots})
          ,\dots,
          (\vv v \circleddash\setof{\vv v,\dots})}
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
  &&  \bigcup(F,\setof{\dots,(e_i\circleddash B_i),\dots})
\\&=& \bigcup(F,\setof{\dots,(e_i\circleddash B_i)\setminus F,\dots}),
      \qquad \because (F \cup A) = (F \cup (A \setminus F))
\\&=& \bigcup(F,\setof{\dots,(e_i\circleddash(B_i \cup F)),\dots})
\\&=& \bigcup(F,\setof{\dots,(e_i\setminus F)\circleddash B_i),\dots})
\\&=& \bigcup(F,\setof{\dots,(e_i\setminus F)\circleddash (B_i\setminus F),\dots})
\end{eqnarray*}
Bascially, there is no need for any element in $F$
to appear in any $\setof{e_i}$ or $B_i$,
as its possible removal by $B_i$ has no effect
on its presence as a free variable.
So we have the following structure: $(F,\setof{\dots,(e_i,B_i),\dots})$
where all $e_i$ are distinct non.-obs. standard variables,
and for all $i$, we have $F \disj (\setof{e_i}\cup B_i)$.

So the picture we now have is:
\begin{eqnarray*}
   \fv &:& T \fun (\Set{V}\times\Set(V\times\Set V)
\\  \fv(\vv v)  &\defs&  (\{\vv v\},\emptyset)
\\ \fv(\bb n {v^+} t) 
   &\defs& 
   (\fv(t)\setminus\setof{\dots,e_i,\dots},\setof{\dots,(e_i,B_i),\dots})
\end{eqnarray*}

\subsection{Need to Record Substitutions?}

A possible definition of free-variables given an explicit substitution is:
\begin{eqnarray*}
   \fv(\ss P {t^n} {r^n})
   &\defs&
   (\fv(P)\setminus{t^n})\cup \fv(rs)
\\ \textbf{where} && rs =  \setof{r | t \in(\fv(P)\cap{t^n}), [r/t] \in [r^n/t^n]}
\end{eqnarray*}
The following example illustrates the problem:
\begin{description}
\item[Law] $P[\lst e/\lst x] = P, \qquad \lst x \notin P$
\item[Goal] $(R[O_m/O'])[O'/O_m], \qquad O',O \supseteq R$.
\item[Bind] 
   $\beta
    =
    \setof{
      P \mapsto R[O_m/O']
      ,
      \lst e \mapsto \seqof{O'}
      ,
      \lst x \mapsto \seqof{O_m}
    }
   $
\end{description}
The issues arises when we try to instantiate the side-condition
$\lst x \notin p$.
This becomes $O_m \notin R[O_m/O']$.
Evaluating this requires computing $\fv(R[O_m/O'])$.
This should proceed as follows:
\begin{eqnarray*}
\lefteqn{\beta(\lst x \disj P)}
\\ &=&  \beta(\lst x) \disj \fv(\beta(P))
\\ &=& \seqof{O_m} \disj \fv(R[O_m/O'])
\\ &=&  \seqof{O_m} \disj (\fv(R)\setminus \setof{O'}) \cup \setof{O_m}
\\ &=&  \seqof{O_m} \disj (\setof{O,O'}\setminus \setof{O'}) \cup \setof{O_m}
        \qquad \text{~uses~} O',O \supseteq R
\\ &=&  \seqof{O_m} \disj (\setof{O} \cup \setof{O_m})
\\ &=&  \seqof{O_m} \disj \setof{O,O_m}
\\ &=&  \false
\end{eqnarray*}
Note that the above demonstration makes use of all available information
when its suits to do so (see ``uses'' comment above).
The problem is the free-variable calculation, 
which has no information about the relationship between $R$, $O'$ and $O_m$.

\textbf{Solution:}
\emph{
  We need to bring side-conditions into this calculation 
  as a context parameter.
}

We then see the following calculation:
\begin{eqnarray*}
\lefteqn{\beta(\lst x \disj P), \qquad  sc = O,O' \supseteq R}
\\ &=&  \beta(\lst x) \disj \fvsc(\beta(P))
\\ &=& \seqof{O_m} \disj \fvsc(R[O_m/O'])
\\ &=& \seqof{O_m} 
       \disj (\fvsc(R) \setminus {O'}) 
             \cup
             \bigcup_{t \in (\fvsc(R)\cap {O'})}^{[r/t] \in [r^n/t^n]}
               \power\fvsc \setof{r}
\\ &=& \seqof{O_m} 
       \disj (\setof{O,O'} \setminus {O'}) 
             \cup
             \bigcup_{t \in (\setof{O,O'}\cap {O'})}^{[r/t] \in [r^n/t^n]}
               \power\fvsc \setof{r}
\\ &=& \seqof{O_m} 
       \disj \setof{O} 
             \cup
             \bigcup_{t \in {O'}}^{[r/t] \in [r^n/t^n]}
               \power\fvsc \setof{r}
\\ &=& \seqof{O_m} \disj \setof{O}  \cup \fvsc(O_m)
\\ &=& \seqof{O_m} \disj \setof{O} \cup \setof{O_m}
\\ &=& \seqof{O_m} \disj \setof{O,O_m}
\\ &=& \false
\end{eqnarray*}


\newpage
\section{Free Variable Definitions}


\begin{code}
type FreeVars = (VarSet, [(GenVar,VarSet)])
\end{code}

The empty free-variable set:
\begin{code}
noFreevars :: FreeVars
noFreevars = ( S.empty, [] )
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
\\&=& ( \setof{\vv y}
      ,
      \setof{ ( \vv f, \setof{\vv x, \vv z} )
              ,
               ( \vv Q, \setof{\vv x, \vv z} )
            })
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
      \qquad \vv x,\vv z \in \vv e, \vv f, \vv P, \vv Q\textrm{ is poss.}
\\&=& ( \setof{\vv y}
      ,
      \setof{ 
        (\vv e, \setof{\vv x, \vv z})
      , (\vv f, \setof{\vv x, \vv z})
      , (\vv P, \setof{\vv x, \vv z})
      , (\vv Q, \setof{\vv x, \vv z})
      })
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
\\&=& ( \setof{\vv y}
      , \setof{
          (\vv f, \setof{\vv x, \vv z})
        , (\vv Q, \setof{\vv x, \vv z})
        } )
\end{eqnarray*}
Here we use $\oplus$ to denote a binary operator that returns the ``union''
of two free-variable sets (details to follow).

In a general setting,
where $X$ denotes sets of observational variables,
and $T$ denotes sets of predicate and expression variables,
we have:
\begin{eqnarray*}
  & & (X_F \sqcup T_F) \ominus (X_B \sqcup T_B)
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
      (V \cup F, \emptyset),     & B\setminus V = \emptyset
   \\ (V, \emptyset),            & F\setminus V = \emptyset
   \\ (V, \setof{((F\setminus V) \circleddash (B\setminus V)}), & \textrm{otherwise}
   \end{array}
   \right.
\end{eqnarray*}
\begin{code}
genFreeVars :: VarSet -> VarSet -> FreeVars
genFreeVars fvs bvs
  | S.null b'  =  (v `S.union` f, [])
  | S.null f'  =  (v, [])
  | otherwise  =  (v, map (subfv b') $ S.toList f')
  where
    (xf,tf) = S.partition isObsGVar fvs  -- (Xf |_| Tf)
    (xb,tb) = S.partition isObsGVar bvs  -- (Xb |_| Tb)
    v = xf S.\\ xb                       -- V = Xf \ Xb
    f = tf S.\\ tb                       -- F = Tf \Tb
    b' = xb S.\\ v                       -- B' = B \ V  = Xb \ V
    f' = f S.\\ v                        -- F' = F \ V
    subfv b v = (v,b)
\end{code}

\newpage

We will need a way to merge these ``sets'' ($\oplus$),
and a way to subtract from them ($sub$).
\begin{eqnarray*}
   \_\oplus\_ &:& \FVE \times \FVE \fun \FVE
\\ (F,\setof{(e_i,B_i)}) \oplus (G,\setof{f_j,C_j})
   &\defs&
   ( F \cup G
   , \setof{(e_i\setminus G,B_i\setminus G)} 
     \cup 
     \setof{f_j\setminus F,C_j\setminus F}
   )
\\ rem_{F} (e,B) &\defs& 
     \emptyset \cond{e \in F} \setof{(e,B\setminus F)}
\end{eqnarray*}
\begin{code}
mrgFreeVars :: FreeVars -> FreeVars -> FreeVars
mrgFreeVars (fvs1,diffs1) (fvs2,diffs2)
  =( fvs1 `S.union` fvs2
   , catMaybes (map (remVarSet fvs2) diffs1 ++ map (remVarSet fvs1) diffs2) 
   )

remVarSet :: VarSet -> (GenVar,VarSet) -> Maybe (GenVar,VarSet)
remVarSet vs (ev,bvs)
  |  ev `S.member` vs  =  Nothing
  |  otherwise         =  Just (ev, bvs S.\\ vs)
\end{code}

We also will want to merge lists of sets:
\begin{code}
mrgFreeVarList :: [FreeVars] -> FreeVars
mrgFreeVarList = foldl' mrgFreeVars noFreevars
\end{code}


\begin{eqnarray*}
   sub &:& \FVE \times \Set{V} \fun \FVE
\\ (F,\setof{(e_i,B_i)}) \setminus S
   &=&
   ( F \setminus S
   ,
     \setof{ (e_i,  (B_i \cup S))}
   )
\\ &=&  (F \ominus S) \oplus (\emptyset, \setof{(e_i, B_i \cup S)})
\end{eqnarray*}
\begin{code}
subVarSet :: FreeVars -> VarSet -> FreeVars
subVarSet (fvs, diffs) vs
 =  mrgFreeVars (genFreeVars fvs vs) (S.empty,map (subMore vs) diffs)
\end{code}

\begin{eqnarray*}
   \_\oslash\_
   &:&
   (V\times\Set{V}) \times \Set{V} \fun V\times\Set{V}
\\ (e,B) \oslash S &\defs& (e,(B \cup S))
\end{eqnarray*}
\begin{code}
-- we flip arguments to facilitate mapping
subMore :: VarSet -> (GenVar,VarSet) -> (GenVar,VarSet)
subMore vs (ev,bvs)  =  (ev,bvs `S.union` vs)
\end{code}

Finally, we need a membership test.
This one returns all those mentioned.
\begin{code}
inFreeVars :: GenVar -> FreeVars -> Bool
inFreeVars gv (fvs,diffs)
  = ( gv `S.member` fvs )
    ||
    ( any (== gv) $ map fst diffs )
\end{code}
Associated with this is the set of all variables satisfying the above predicate:
\begin{code}
theFreeVars :: FreeVars -> VarSet
theFreeVars (fvs,diffs) = fvs `S.union` ( S.fromList $ map fst diffs )
\end{code}


\newpage

\section{Term Free Variables}

\begin{eqnarray*}
   \fvsc(\kk k)  &\defs&  \emptyset
\\ \fvsc(\vv v)  &\defs&  \{\vv v\} \quad \mbox{$v$ is non-textual}
\\ \fvsc(\vv P)  &\defs&  V \cond{(V \supseteq P) \in sc} \{\vv P\} 
\\ \fvsc(\cc n {ts}) &\defs& \bigcup_{t \in ts} \fvsc(t)
\\ \fvsc(\bb n {v^+} t) &\defs& \fvsc(t)\setminus{v^+}
\\ \fvsc(\ll n {v^+} t) &\defs& \fvsc(t)\setminus{v^+}
\\ \fvsc(\ii \bigoplus n {lvs}) &\defs& lvs
   \quad \mbox{less any textual list-vars in }lvs
\\ \fvsc(\ss P {t^n} {r^n})
   &\defs&
   (\fvsc(P)\setminus{t^n})\cup \fvsc(rs)
\\ \textbf{where} && rs =  \setof{r | t \in(\fvsc(P)\cap{t^n}), [r/t] \in [r^n/t^n]}
\end{eqnarray*}
\begin{code}
notTextualLV (LVbl (Vbl _ _ vw) _ _) = vw /= Textual

freeVars :: SideCond -> Term -> FreeVars
freeVars _ (Val _ _)  =  noFreevars
freeVars sc (Var tk v@(Vbl _ ObsV vw))
  | vw /= Textual  =  injVarSet $ S.singleton $ StdVar v
  | otherwise      =  noFreevars
freeVars sc (Var tk p@(Vbl _ _ vw)) -- not ObsV
  = case findCoveredGenVar vP sc of
      Nothing     ->  injVarSet $ S.singleton vP
      Just cover  ->  injVarSet cover
  where  vP = StdVar p
freeVars sc (Cons tk sb n ts)  =  mrgFreeVarList $ map (freeVars sc) ts
freeVars sc (Bnd tk n vs tm)   =  subVarSet (freeVars sc tm) vs
freeVars sc (Lam tk n vl tm)   =  subVarSet (freeVars sc tm) $ S.fromList vl
freeVars sc (Cls _ _)          =  noFreevars

freeVars sc (Iter tk sa na si ni lvs)
  =  injVarSet $ S.fromList $ map LstVar $ filter notTextualLV lvs
\end{code}

\subsection{Assignment Free Variables}

We use the substitution to model assignment:
$$
v,\lst v :=  e,\lst e   
 \quad\defs\quad   (:=)[e,\lst e/x,\lst x]
$$
\begin{code}
freeVars sc (Sub tk tm (Substn vts lvlvs))
  | isAssignment tm
      = (foldl' mrgFreeVars noFreevars (S.map (freeVars sc) ts))
         `mrgFreeVars`
         (injVarSet (vs `S.union` lvs1 `S.union` lvs2))
      where
         ts = S.map snd vts
         vs = S.map (StdVar . fst) vts
         lvs1 = S.map (LstVar . fst) lvlvs
         lvs2 = S.map (LstVar . snd) lvlvs
\end{code}

\newpage
\subsection{Substitution Free Variables}

Substitution is complicated, so here's a reminder:
\begin{eqnarray*}
   \fvsc(\ss P {t^n} {r^n})
   &\defs&
   (\fvsc(P)\setminus{t^n})\cup \fvsc(rs)
\\ \textbf{where} && rs =  \setof{r | t \in(\fvsc(P)\cap{t^n}), [r/t] \in [r^n/t^n]}
\end{eqnarray*}
This function returns the free variables in a substitution
\emph{relative} to a given term to which it is being applied.
It also returns the free variables from that term that will be substituted for.
We expect the following to hold:
$$
\fvsc(R[O_m/O']) =  (\setof{O_m},\setof{(R,\setof{O'})}) 
$$
We can imagine the following process to compute $\fvsc(P[r^n/t^n])$ :
\begin{itemize}
   \item Let $fvp = \fvsc(P)$.
   \item Let $vistgt = t^n \cap fvp$.
   \item Let $visrepl = r^n | vistgt$.
   \item Let $visfvs = \cup/\power\fvsc(visrepl)$.
   \item Produce $visfvs \cup (fvp \setminus t^n)$.
\end{itemize}

\begin{code}
freeVars sc (Sub tk tm sub)
  = let
      fvtm = freeVars sc tm
      (vistgt,visfvs) = substRelFree sc fvtm sub
      missed = subVarSet fvtm (subTargets sub)
    in mrgFreeVars visfvs missed
\end{code}

In all other cases we return an empty set:
\begin{code}
freeVars _ _ = noFreevars
\end{code}

What does \texttt{substRelFree} do?
Given free variables $fv$, and a substitution,
it selects pairs whose targets are in $fv$,
returns the target variables in a set,
and builds a new free-variables result out of the free-variables of all the
replacements. 
$$
sRF~\setof{x,u,\lst u}~[e,f,\lst e,lst f/u,v,\lst u,\lst v]
=
(\setof{u,\lst u},\fvsc(e) \cup \setof{\lst e})
$$
This is $(vistgt,visfvs)$ from above.
\begin{code}   
substRelFree :: SideCond -> FreeVars -> Substn -> (VarSet,FreeVars)
substRelFree sc tfv (Substn ts lvs) = (tgtvs,rplvs)
 where
   ts' = S.filter (applicable StdVar tfv) ts
   lvs' = S.filter (applicable LstVar tfv) lvs
   tgtvs = S.map (StdVar . fst) ts'
           `S.union`
           S.map (LstVar . fst) lvs'
   rplvs = ( mrgFreeVarList $ S.toList $ S.map (freeVars sc . snd) ts' )
           `mrgFreeVars`
           ( injVarSet $ S.map (LstVar .snd) lvs' )
\end{code}
A target/replacement pair is ``applicable'' if the target variable
is in the free variables of the term being substituted.
\begin{code}
applicable :: (tgt -> GenVar) -> FreeVars -> (tgt,rpl) -> Bool
applicable toGV tfv (t,_) = toGV t `inFreeVars` tfv
\end{code}

\newpage
\section{Quantifier Nesting}

Support for quantifier nesting needs to be hardwired in.

\subsection{Zeroing a term}

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

zeroLVarIdNumber :: ListVar -> ListVar
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

\subsection{Nesting Simplification}

So we have to hardwire the basic simplification laws:
\begin{eqnarray*}
   (\bb n {V_i }{\bb n {V_j} P})
   &=& (\bb n {(V_i \cup V_j)}  P)
\\ (\bb i {V_i} {\bb j {V_j} P)}
   &=& \bb j {V_j}  P, \qquad\qquad\qquad\qquad\quad \IF ~V_i \subseteq V_j~,
\\ &=& (\bb i {(V_i\setminus V_j)} {\bb j {V_j}  P}), \qquad \otherwise.
\\ (\ll n {\sigma_i } {\ll n {\sigma_j \cat \sigma_k} P})
   &=& (\ll n {(\sigma_i \cat \sigma_j)}  {\ll n {\sigma_k} P}),
       \qquad \elems \sigma_i \disj \elems \sigma_j
\end{eqnarray*}
Function \texttt{nestSimplify} returns a simplified term
if one of the laws above applies, otherwise it fails.
\begin{code}
nestSimplify :: MonadFail m => Term -> m Term

nestSimplify (Bnd tk1 n1 vs1 t1@(Bnd tk2 n2 vs2 t2))
 | tk1 /= tk2              =  fail ("nestSimplify: mixed bind term-kinds")
 | vs1 `S.isSubsetOf` vs2  =  return t1
 | n1 /= n2                =  bnd tk1 n1 (vs1 S.\\ vs2) t2
 | otherwise               =  bnd tk1 n1 (vs1 `S.union` vs2) t2

nestSimplify (Lam tk1 n1 vl1 (Lam tk2 n2 vl2 t2))
 | tk1 /= tk2  =  fail ("nestSimplify: mixed lambda term-kinds")
 | n1  == n2   =  lam tk1 n1 (vl1 ++ vl2) t2
 | otherwise   =  fail ("nestSimplify: mixed lambda forms")

nestSimplify trm = fail "nestSimplify: not nested similar quantifiers"
\end{code}


\newpage

\section{Tests}

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
