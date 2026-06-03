\chapter{Variable-Set Expressions}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2026

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module VarSetExpr (
  VSetExpr(..)
, VSetPred(..)
, vsEmpty, vsSngl, vsUnion, vsMinus
, simplifyVSetPred
) where
import Data.Maybe
-- import Data.Either (lefts,rights)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List

import NotApplicable
import Utilities
import Control
import Symbols
import UnivSets
import LexBase
import Variables
import Types
import AST
--import SideCond
--import Binding
--import Matching
--import FreeVars
--import VarData
--import TestRendering

import Debugger
\end{code}

\section{Introduction}

We provide set-expressions and predicates tailored for writing  and analysing side-conditions involving general variables.


\newpage
\section{Variable-Set Term Syntax}

We assume our basic building block to be enumerations of general variables:
$$\setof{gv_1,\dots,gv_n}, \qquad n \geq 0 .$$
These can then be combined with set-theoretic operators 
($\cup$,$\cap$,$\setminus$) 
to produce set expressions.
We then add set-theoretic relations 
($=$,$\supseteq$,$\disj$) 
over such expressions, to produce set predicates.

\subsection{Variable-Set Datatypes}

\begin{code}
data VSetExpr 
  =  VSEnum   VarSet             
  |  VSUnion  VSetExpr VSetExpr  
  |  VSIntsct VSetExpr VSetExpr
  |  VSMinus  VSetExpr VSetExpr 
  deriving (Eq,Ord,Show)

data VSetPred
  =  VSTrueP
  |  VSDisj  VSetExpr VSetExpr  -- relation on sets
  |  VSSub   VSetExpr VSetExpr  -- relation on sets
  |  VSSubD  VSetExpr VSetExpr  -- relation on sets limited to dynamic vars
  deriving (Eq,Ord,Show)
\end{code}


\section{Smart Variable-Set Constructors}

Empty and singleton sets:
\begin{code}
vsEmpty :: VSetExpr
vsEmpty = VSEnum S.empty

vsSngl :: GenVar -> VSetExpr
vsSngl = VSEnum . S.singleton
\end{code}

We do the obvious simplifications for enumeration, union and removal.
\begin{code}
vsUnion :: VSetExpr -> VSetExpr -> VSetExpr
vsUnion (VSEnum vs1) (VSEnum vs2) = VSEnum (vs1 `S.union` vs2)
vsUnion vse1 vse2
  | vse1 == vsEmpty  =  vse2
  | vse2 == vsEmpty  =  vse1
  | otherwise        =  VSUnion vse1 vse2

vsIntsct :: VSetExpr -> VSetExpr -> VSetExpr
vsIntsct (VSEnum vs1) (VSEnum vs2) = VSEnum (vs1 `S.intersection` vs2)
vsIntsct vse1 vse2
  | vse1 == vsEmpty  =  vsEmpty
  | vse2 == vsEmpty  =  vsEmpty
  | otherwise        =  VSIntsct vse1 vse2

vsMinus :: VSetExpr -> VSetExpr -> VSetExpr
vsMinus vsplus vsminus
  | vsplus  == vsminus  =  vsEmpty
  | vsplus  == vsEmpty  =  vsplus
  | vsminus == vsEmpty  =  vsplus
  | otherwise           =  VSMinus vsplus vsminus
\end{code}

\textbf{Smart VSetPred constructors?}

\newpage
\section{Simplifying Set-Predicates}

\textbf{Changed from using superset to using subset}
\emph{
  What we see eveywhere are $s,s'\supseteq_a P$,
   and it is easier to have $P \subseteq s,s'$.
}

\begin{eqnarray*}
   \setof{O,O'} \supseteq \setof{ls,ls',a} 
   \land \setof{O,O'} \supseteq \setof{a}
   &=& \setof{O,O'} \supseteq \setof{ls,ls',a}
\\ (P\setminus \lst y) \disj \lst x 
   &=&
   \setof{P} \disj (\lst x \setminus \lst y) 
\\ \lst y \supseteq \lst x &\implies& (\lst x \setminus \lst y) = \emptyset
\end{eqnarray*}

Here we are generally interested in single relations ($\disj$,$\supseteq$)
with a single distinguished term variable $P$ embedded inside set operations ($\cup$,$\setminus$).
We want to pull $P$ out to be the sole 1st argument of the relation.
These should \emph{not} reduce the relations to \true\ or \false.
In general we may need extra terms not involving $P$ in the output.
We want to distinguish therse so we keep them separate.
\begin{code}
simplifyVSetPred :: VSetPred -> (VSetPred,[VSetPred])
\end{code}  

\subsection{Union and Diff vs. Disjoint and Superset}

$$(P \setminus X) \disj Y ~=~ P \disj (Y \setminus X)$$
\begin{code}
simplifyVSetPred ((p `VSMinus` x) `VSDisj` y)  
             =  (p `VSDisj` (y `vsMinus` x), [])
\end{code} 

$$ 
   (P \cup X) \disj Y 
   ~=~ 
   (P \disj Y) \land (X \disj Y)
$$
\begin{code}
simplifyVSetPred ((p `VSUnion` x) `VSDisj` y)  
               = (p `VSDisj` y , [x `VSDisj` y ] )
\end{code} 

$$  
   P \subseteq (X \setminus Y) 
   ~=~ 
   ?
$$
\begin{code}
simplifyVSetPred (y `VSSub` (p `VSMinus` x)) 
  = ( p `VSSub` (y `vsMinus` x) , [x `VSDisj` y  ] )
\end{code} 

$$ P \subseteq (X \cup Y)
   ~=~ 
   ?
$$
\begin{code}
simplifyVSetPred ((p `VSUnion` x) `VSSub` y)  
             =  (p `VSSub` (y `vsMinus` x), [])
\end{code} 


\subsection{Union and Diff vs. Dynamic Superset}

Dynamic superset ($\supseteq_d$) is defined as:
$$
  P \supseteq_d X \quad \defs \quad P|d \supseteq X|d
$$
where $S|d$ is $S$ restricted to the dynamic variables in $d$.
The key question is: does this affect the laws?
The answer is no, because being dynamic is a pointwise property
and restriction w.r.t a set element (or sets of elements) is idempotent.
\begin{eqnarray*}
   \emptyset|d &\defs& \emptyset
\\ \setof{x}|d &\defs& \setof{x} \cond{x \in d} \emptyset
\\ (S\cup T)|d &\defs& S|d \cup T|d
\\ (S\cap T)|d &\defs& S|d \cap T|d
\\ (S\setminus T)|d &\defs& S|d \setminus T|d
\end{eqnarray*}

$$  
   (P \setminus X) \supseteq_d Y 
   ~=~ 
   P \supseteq_d (Y \setminus X) \land (X \disj Y)
$$
\begin{code}
simplifyVSetPred ((p `VSMinus` x) `VSSubD` y) 
  = ( p `VSSubD` (y `vsMinus` x) , [x `VSDisj` y  ] )
\end{code} 

$$ (P \cup X) \supseteq_d Y 
   ~=~ 
   P \supseteq_d (Y \setminus X)
$$
\begin{code}
simplifyVSetPred ((p `VSUnion` x) `VSSubD` y)  
             =  (p `VSSubD` (y `vsMinus` x), [])
\end{code} 

\subsection{All other cases: no change}

For now we notice that that none of the laws above
introduce intersections or disjunctions.
We'll only add laws about those if they arise elsewhere.
\begin{code}
simplifyVSetPred vse = (vse,[]) 
\end{code}  

