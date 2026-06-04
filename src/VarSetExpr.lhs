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
, vsEmpty, vsSngl, vsUnion, vsMinus, vSetVars
, vsFalse, vsTrue, vsDisj, vsSub, vsSubD, vPredVars
) where
import Data.Set(Set)
import qualified Data.Set as S
import Variables

import Debugger
\end{code}

\section{Introduction}

We provide set-expressions and predicates built over \h{VarSet},
along with constructors and simplifiers.


\newpage
\section{Variable-Set Term Syntax}

We assume our basic building blocks to be enumerations of general variables:
$$\setof{gv_1,\dots,gv_n}, \qquad n \geq 0 .$$
These can then be combined with set-theoretic operators 
($\cup$,$\cap$,$\setminus$) 
to produce set expressions.
We then add set-theoretic relations 
($=$,$\subseteq$,$\disj$) 
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
  =  VSFalseP -- yes, we need this
  |  VSDisj  VSetExpr VSetExpr  
  |  VSSub   VSetExpr VSetExpr 
  |  VSSubD  VSetExpr VSetExpr  -- limited to dynamic vars
  |  VSTrueP
  deriving (Eq,Ord,Show)
\end{code}

\section{Smart Set Expression Constructors}

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

\section{Set Expression Queries}

Just collect all mentioned variables
\begin{code}
vSetVars :: VSetExpr -> VarSet
vSetVars (VSEnum gvs)          =  gvs
vSetVars (VSUnion vse1 vse2)   =  vSetVars vse1 `S.union` vSetVars vse2
vSetVars (VSIntsct vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vSetVars (VSMinus vse1 vse2)   =  vSetVars vse1 `S.union` vSetVars vse2
\end{code}

\section{Simplifying Set Expressions}

\section{Smart Set Predicate constructors}

\begin{code}
vsFalse :: VSetPred
vsFalse = VSFalseP

vsTrue :: VSetPred
vsTrue = VSTrueP

vsDisj :: VSetExpr -> VSetExpr -> VSetPred
vsDisj (VSEnum vs1) (VSEnum vs2) 
  | vs1 `S.disjoint` vs2  =  VSTrueP
  | otherwise             =  VSFalseP
vsDisj vse1 vse2          =  VSDisj vse1 vse2
-- vse1==vse2 implies disjoint if both are empty  

vsSub :: VSetExpr -> VSetExpr -> VSetPred
vsSub (VSEnum vs1) (VSEnum vs2)
  | vs1 `S.isSubsetOf` vs2  =  VSTrueP
  | otherwise               =  VSFalseP
vsSub vse1 vse2             =  VSSub vse1 vse2

vsSubD :: VSetExpr -> VSetExpr -> VSetPred
vsSubD (VSEnum vs1) (VSEnum vs2)
  | vs1d `S.isSubsetOf` vs2d  =  VSTrueP
  | otherwise                 =  VSFalseP
  where
    vs1d = S.filter isDynGVar vs1
    vs2d = S.filter isDynGVar vs2
vsSubD vse1 vse2              =  VSSubD vse1 vse2
\end{code}


\section{Set Predicate Queries}

\begin{code}
vPredVars :: VSetPred -> VarSet
vPredVars (VSDisj vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vPredVars (VSSub  vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vPredVars (VSSubD vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vPredVars _                   =  S.empty
\end{code}

\section{Simplifying Set Predicates}





