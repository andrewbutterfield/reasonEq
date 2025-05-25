\chapter{Abstract Types}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017-2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Types ( Type
           , isAtmType
           , bool, arbpred
           , pattern ArbType,  pattern TypeVar, pattern TypeCons
           , pattern AlgType, pattern FunType, pattern GivenType
           , pattern BottomType
           , isPType, isEType
           , isSubTypeOf, reconcile2Types, reconcileTypes
           ) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import LexBase
import Variables

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}

\section{Types}

We mainly use types to prevent large numbers of spurious matches
occurring with expressions.

We have the following type expressions:
\begin{description}
  \item [Arbitrary] $\top$, most general, or \emph{universal} (a.k.a. ``top'').
  \item [Variables] $n$.
  \item [Constructors] $n(\tau,\dots)$.
  \item [Algebraic] $n\seqof{n(\tau,\dots)}$, can be recursive.
  \item [Given] $\gg g$.
  \item [Bottom] $\bot$, the empty type.
\end{description}


\begin{eqnarray*}
   t,TC,DT,DC &\in& Name
\\ \tau \in Type &::=& \top 
                  \mid t 
                  \mid TC(\tau,\dots)
                  \mid DT\seqof{DC(\tau,\dots)}
                  \mid \tau\fun\tau
                  \mid \gg g 
                  \mid \bot
\end{eqnarray*}


\begin{code}
data Type -- most general types first
 = T  -- arbitrary type -- top of sub-type relation
 | TV Identifier -- type variable
 | TC Identifier [Type] -- type constructor, applied
 | TA Identifier [(Identifier,[Type])] -- algebraic data type
 | TF Type Type -- function type
 | TG Identifier -- given type
 | TB -- bottom type,  bottom of sub-type relation
 deriving (Eq, Ord, Show, Read)

isAtmType :: Type -> Bool
isAtmType T       =  True
isAtmType (TV _)  =  True
isAtmType (TG _)  =  True
isAtmType TB      =  True
\end{code}
The ordering of data-constructors here is important,
as type-matching relies on it. \textbf{How?}


\begin{code}
pattern ArbType = T
pattern TypeVar i  = TV i
pattern TypeCons i ts = TC i ts
pattern AlgType i fs = TA i fs
pattern FunType td tr = TF td tr
pattern GivenType i = TG i
pattern BottomType = TB

bool  = TG $ jId $ "B"
arbpred = TF TB bool -- top of the predicate subtype lattice (see below)

-- isPtype t if t has shape  t1 -> t2 -> ... -> tn -> bool
-- which is really t1 -> (t2 -> (... -> (tn -> bool)...))
lasttype (TF _ tr)  =  lasttype tr
lasttype t          =  t

isPType (TF _ t)  =  lasttype t == bool
isPType _         =  False
isEType           =  not . isPType
\end{code}

\subsection{Sub-Typing}

We say that $\tau_1$ is a subtype of $\tau_2$ ($\tau_1\subseteq_T\tau_2$)
if every value in $\tau_1$ is also in $\tau_2$.
This means we can use a value of type $\tau_1$ whenever a value of type $\tau_2$ is expected.
We can immediately identify the following laws:
\begin{eqnarray*}
   \tau &\subseteq_T& \top
\\ t_1 &\subseteq_T& t_2 ~~\where~~ t_1=t_2
\\ TC(\tau_1,\dots,\tau_n) 
   &\subseteq_T& 
   TC(\tau'_1,\dots,\tau'_n) ~~\where~~ \forall i . \tau_i \subseteq_T \tau'_i, 
\\ DT(\seqof{TC_1(\dots),\dots,TC_n(\dots)})
   &\subseteq_T& 
   DT(\seqof{TC_1(\dots'),\dots,TC_n(\dots'),\dots}) 
\\ && \where~~ \forall i . TC_i(\dots) \subseteq_T TC_i(\dots') 
\\ \tau_{a_1} \fun \tau_{r_1} &\subseteq_T& \tau_{a_2} \fun \tau_{r_2}
   ~~\where~~ \tau_{a_2} \subseteq_T \tau_{a_1} 
            \land
            \tau_{r_1} \subseteq_T \tau_{r_2}
\\ \gg{g}   &\subseteq_T& t
\\ \gg{g}_1 &\subseteq_T& \gg{g}_2 ~~\where~~ \gg{g}_1=\gg{g}_2
\\ \bot &\subseteq_T& \tau
\end{eqnarray*}
Note that $t$, $TC()$, and $DT\seqof{}$ are mutually incomparable,
and also the contravariance of the function argument types.
Given a mix of type-variables and given-types,
we assume the latter are subtypes of the former for now
(\textsl{~this hopefully won't interact too badly with type-inference~}!)
The contravariance extends to higher-order functions as follows:
$$
\sigma_1 \fun \dots \sigma_{n-1} \fun \sigma_n
~\subseteq_T~
\tau_1 \fun \dots \tau_{n-1} \fun \tau_n
$$
is equivalent to:
$$
 \tau_1 \subseteq_T \sigma_1 
 ~\land~
 \dots
 ~\land~
 \tau_{n-1} \subseteq_T \sigma_{n-1}
 ~\land~
 \sigma_n \subseteq_T \tau_n
$$
In the type system here, an expression of type bool,
has its type represented by $\Bool$,
while predicates have a type of the form $t1\fun \dots tn \fun \Bool$.
For subtyping below these should be treated as the same,
so we extend our relation by adding:
\begin{eqnarray*}
   \Bool &\subseteq_T& \bot\fun\Bool
\\ \tau \fun \Bool &\subseteq_T& \bot\fun\Bool
\\ \tau_1 \fun \tau_2 \fun \Bool &\subseteq_T& \bot\fun\Bool
\\  &\vdots
\end{eqnarray*}
\begin{code}



isSubTypeOf :: Type -> Type -> Bool
isSubTypeOf t1 t2
  | lasttype t1 == bool && t2 == arbpred  =  True
  | otherwise                             =  t1 `isSTOf` t2

isSTOf :: Type -> Type -> Bool
-- true outcomes first, to catch t==t case
_            `isSTOf` T        =  True
T            `isSTOf` _        =  False
TB           `isSTOf` _        =  True
_            `isSTOf` TB       =  False
(TV i1)      `isSTOf` (TV i2)  =  i1 == i2
(TG _)       `isSTOf` (TV _)   =  True
(TG i1)      `isSTOf` (TG i2)  =  i1 == i2
(TC i1 ts1)  `isSTOf` (TC i2 ts2) | i1==i2 = ts1 `areSTOf` ts2
(TA i1 fs1)  `isSTOf` (TA i2 fs2) | i1==i2 = fs1 `areSFOf` fs2
(TF td1 tr1) `isSTOf` (TF td2 tr2)  
                               =  td2 `isSTOf` td1 && tr1 `isSTOf` tr2
_            `isSTOf` _        = False
\end{code}
\textbf{NOTE: }
\textsl{What if $t_1$ is a type-variable $t$ while $t_2$ is a given type $\mathbb{G}$?}


\begin{code}
areSTOf :: [Type] -> [Type] -> Bool -- are SubTypesOf
[]       `areSTOf` []        =  True
(t1:ts1) `areSTOf` (t2:ts2)  =  t1 `isSTOf` t2 && ts1 `areSTOf` ts2
_        `areSTOf` _         =  False
\end{code}

\begin{code}
-- areSubFieldsOf
areSFOf :: [(Identifier,[Type])] -> [(Identifier,[Type])] -> Bool
[] `areSFOf` []  =  True
((i1,ts1):fs1) `areSFOf` ((i2,ts2):fs2)
 | i1 == i2      =  ts1 `areSTOf` ts2 && fs1 `areSFOf` fs2
_ `areSFOf` _    =  False
\end{code}

We also need to reconcile a pair of types, 
returning a type that is at least as general as both.
\begin{code}
reconcile2Types :: Type -> Type -> Type
reconcile2Types t1 t2 
  |  t1 `isSubTypeOf` t2  =  t2
  |  t2 `isSubTypeOf` t1  =  t1
  |  otherwise            =  T

reconcileTypes :: [Type] -> Type
reconcileTypes = foldl reconcile2Types TB
\end{code}
This is a course-grained approximation, but adequate for most purposes.

