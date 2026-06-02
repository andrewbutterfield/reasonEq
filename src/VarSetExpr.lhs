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
, trVSPred
, vsEmpty, vsSngl, vsUnion, vsMinus
, simplifyVSetPred
, fvs2vses, diff2vses
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
import SideCond
import Binding
import Matching
import FreeVars
import VarData
import TestRendering

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
  |  VSSup   VSetExpr VSetExpr  -- relation on sets
  |  VSSupD   VSetExpr VSetExpr  -- relation on sets limited to dynamic vars
  deriving (Eq,Ord,Show)
\end{code}

\subsection{Rendering Variable-Sets}

Empty and singleton sets:
\begin{code}
trVSExpr = trvsexpr trId
trVSExprU = trvsexpr trIdU
trvsexpr trid (VSEnum vse) 
  | sz == 0    =  _emptyset
  | sz == 1    =  trgvar trid $ head $ S.toList vse
  | otherwise  =  trvset trid vse 
  where sz = S.size vse
trvsexpr trid (VSUnion vse1 vse2) 
  = "("++trvsexpr trid vse1++_union++trvsexpr trid vse2++")"
trvsexpr trid (VSIntsct vse1 vse2) 
  = "("++trvsexpr trid vse1++_intsct++trvsexpr trid vse2++")"
trvsexpr trid (VSMinus vse1 vse2) 
  = "("++trvsexpr trid vse1++_setminus++trvsexpr trid vse2++")"

trvsets trid = seplist "," $ trvset trid

vsedbg = rdbg trVSExpr
vsesdbg = rdbg (seplist ";" $ trVSExpr)

trVSPred = trvspred trId
trVSPredU = trvspred trIdU
trvspred trid VSTrueP = "true"
trvspred trid (VSDisj vse1 vse2) 
  = "("++trvsexpr trid vse1++_disj++trvsexpr trid vse2++")"
trvspred trid (VSSup vse1 vse2) 
  = "("++trvsexpr trid vse1++_supseteq++trvsexpr trid vse2++")"
trvspred trid (VSSupD vse1 vse2) 
  = "("++trvsexpr trid vse1++_supseteq++_subStr "a"++trvsexpr trid vse2++")"

trvspreds trid = seplist "," $ trvspred trid

vspdbg = rdbg trVSPred
vspsdbg = rdbg (seplist "_land" $ trVSPred)
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


\section{Simplifying Set-Predicates}

\begin{eqnarray*}
   \setof{O,O'} \supseteq \setof{ls,ls',a} 
   \land \setof{O,O'} \supseteq \setof{a}
   &=& \setof{O,O'} \supseteq \setof{ls,ls',a}
\\ (P\setminus \lst y) \disj \lst x 
   &=&
   \setof{P} \disj (\lst x \setminus \lst y) 
\\ \lst y \supseteq \lst x &\implies& (\lst x \setminus \lst y) = \emptyset
\end{eqnarray*}

Here we are interested in single relations ($\disj$,$\supseteq$)
with a single distinguished term variable $P$ embedded inside set operations ($\cup$,$\setminus$).
We want to pull $P$ out to be the sole 1st argument of the relation.
These should \emph{not} reduce the relations to \true\ or \false.
In general we may need extra terms not involving $P$ in the output.
We want to distinguish there so we keep them separate.
\begin{code}
simplifyVSetPred :: VSetPred -> (VSetPred,[VSetPred])
\end{code}  
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
   (P \setminus X) \supseteq Y 
   ~=~ 
   P \supseteq (Y \setminus X) \land (X \disj Y)
$$
\begin{code}
simplifyVSetPred ((p `VSMinus` x) `VSSup` y) 
  = ( p `VSSup` (y `vsMinus` x) , [x `VSDisj` y  ] )
\end{code} 
$$ (P \cup X) \supseteq Y 
   ~=~ 
   P \supseteq (Y \setminus X)
$$
\begin{code}
simplifyVSetPred ((p `VSUnion` x) `VSSup` y)  
             =  (p `VSSup` (y `vsMinus` x), [])
\end{code} 
All other cases: no change 
\begin{code}
simplifyVSetPred vse = (vse,[]) 
\end{code}  

\section{Converting Free-Variables to Variable-Sets}

Here we convert free-variables into set-expressions:
\begin{code}
fvs2vses :: FreeVars -> VSetExpr
fvs2vses (fvs,diffs) 
  = foldl vsUnion (VSEnum fvs) (map diff2vses diffs)

diff2vses :: (GenVar,VarSet) -> VSetExpr
diff2vses (gv,vs) = vsMinus (vsSngl gv) (VSEnum vs)
\end{code}


