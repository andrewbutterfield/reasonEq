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
, vsEmpty, vsSngl, vsList, vsUnion, vsMinus
, vSetVars, theGV
, vsFalse, vsTrue, vsDisj, vsSub, vsSubD, vPredVars
, enumSamePred
) where
import Data.Char(isSpace)
import Data.Set(Set)
import qualified Data.Set as S
import LexBase
import Variables

import Debugger
\end{code}

\section{Introduction}

We provide set-expressions and predicates built over \h{VarSet},
along with constructors and simplifiers.
We assume our basic building blocks to be enumerations of general variables:
$$\setof{gv_1,\dots,gv_n}, \qquad n \geq 0 .$$
These can then be combined with set-theoretic operators 
($\cup$,$\cap$,$\setminus$) 
to produce set expressions.
We then add set-theoretic relations 
($=$,$\subseteq$,$\disj$) 
over such expressions, to produce set predicates.

\section{Variable-Set Expressions}

Given that we want to use \h{Show} \emph{and \h{Read}} for save and restore,
we develop a bespoke \h{Read} for \h{VarSet}.

\begin{code}
data VSetExpr 
  =  VSEnum   VarSet             
  |  VSUnion  VSetExpr VSetExpr  
  |  VSIntsct VSetExpr VSetExpr
  |  VSMinus  VSetExpr VSetExpr 
  deriving (Eq,Ord,Show)

instance Read VSetExpr where
  readsPrec _ str = [readVListExpr str]

bad_res msg = vsSngl $ StdVar $ PredVar (jId msg) Static
bad_VSetExpr str = bad_res ("BAD_VSetExpr_"++map clean(take 5 str))
clean c = if isIdContChar c then c else '?'
bad_NYI str = bad_res (str++"_NYI")

readVListExpr :: String -> (VSetExpr,String)
-- expect VS to begin
readVListExpr (c:str) | isSpace c = readVListExpr str
readVListExpr ('V':'S':str) = readVExprKind str
readVListExpr str = (bad_VSetExpr str,str)

readVExprKind :: String -> (VSetExpr, String)
-- seen VS
-- expect Enum|Union|Intsct|Minus
readVExprKind str
  | before4 == "Enum"   = readPar   readEnum after4
  | before5 == "Union"  = read2Sets VSUnion  after5
  | before6 == "Intsct" = read2Sets VSIntsct after6
  | before5 == "Minus"  = read2Sets VSMinus  after5
  | otherwise           = (bad_res "invalid_set_constructor",str)
  where 
   (before4,after4) = splitAt 4 str
   (before5,after5) = splitAt 5 str
   (before6,after6) = splitAt 6 str

readPar :: (String -> (VSetExpr, String)) -> String 
        -> (VSetExpr, String)
-- expect ( something )
readPar readSomeThing (c:str) | isSpace c = readPar readSomeThing str
readPar readSomeThing ('(':str) 
 = let (thing,str') = readSomeThing str in 
     case str' of
        (')':str'')  ->  (thing,str'')
        _            ->  (bad_res "missing_rpar",str')
readPar _ str = (bad_res "missing_lpar",str)

readEnum :: String -> (VSetExpr, String)
-- expect fromList [ ... ]
readEnum str
  | before == "fromList " 
    = case readsPrec 0 after of
        ((varlist,str'):_)  -> ((VSEnum $ S.fromList varlist),str')
        _             -> (bad_NYI "missing_varlist_1",str)
  where (before,after) = splitAt 9 str
readEnum str = (bad_res "missing_varlist_2",str)

read2Sets :: (VSetExpr -> VSetExpr -> VSetExpr) 
          -> String -> (VSetExpr,String)
read2Sets make str0 
  = let (set1,str1) = readPar readVListExpr str0
    in case str1 of
         (' ':str1') 
            ->  let (set2,str2) = readPar readVListExpr str1'
                in (make set1 set2,str2)
         _  ->  (bad_res "missing_space_between_2_sets",str1)

vE  = ExprVar (jId "E") Static ; gE  = StdVar vE  ; sE  = vsSngl gE
vN  = ExprVar (jId "N") Static ; gN  = StdVar vN  ; sN  = vsSngl gN
vx  = ObsVar  (jId "x") Before ; gx  = StdVar vx  ; sx  = vsSngl gx
vx' = ObsVar  (jId "x") After  ; gx' = StdVar vx' ; sx' = vsSngl gx'
sEdN  = VSDisj sE sN
sEsN  = VSSub  sE sN
sEsdN = VSSubD sE sN
\end{code}

\subsection{Smart Set Expression Constructors}

Empty and singleton sets:
\begin{code}
vsEmpty :: VSetExpr
vsEmpty = VSEnum S.empty

vsSngl :: GenVar -> VSetExpr
vsSngl = VSEnum . S.singleton

vsList :: VarList -> VSetExpr
vsList = VSEnum . S.fromList
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

\subsection{Set Expression Queries}

Just collect all mentioned variables
\begin{code}
vSetVars :: VSetExpr -> VarSet
vSetVars (VSEnum gvs)          =  gvs
vSetVars (VSUnion vse1 vse2)   =  vSetVars vse1 `S.union` vSetVars vse2
vSetVars (VSIntsct vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vSetVars (VSMinus vse1 vse2)   =  vSetVars vse1 `S.union` vSetVars vse2
\end{code}

Extract ``the'' general variable:
\begin{code}
theGV :: MonadFail mf => VSetExpr -> mf GenVar
theGV (VSEnum gvs) = case S.toList gvs of
  [gv]     ->  return gv
  _        ->  fail "theGV: singleton enumeration expected"
theGV vse  =  fail "theGV: singleton enumeration expected"
\end{code}

\subsection{Simplifying Set Expressions}

T.B.D.

\section{Variable-Set Predicates}

We want predicates that relate two set-expressions.
The relations that we want are 
disjointness ($\disj$),
subset ($\subseteq$),
and a version of subset restricted to dynamic variables ($\subseteq_d$).
Dynamic subset ($\subseteq_d$) is defined as:
$$
  g \subseteq_d X \quad \defs \quad g|d \subseteq X|d
$$
where $S|d$ is $S$ restricted to the dynamic variables in scope.
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


\begin{code}
data VSetPred
  =  VSFalseP -- yes, we need this
  |  VSDisj  VSetExpr VSetExpr  
  |  VSSub   VSetExpr VSetExpr 
  |  VSSubD  VSetExpr VSetExpr  -- limited to dynamic vars
  |  VSTrueP
  deriving (Eq,Ord,Show)

instance Read VSetPred where
  readsPrec _ str = [readVListPred str]

bad_VSetPred str 
  =  VSSub (bad_res ("BAD_VSetPred_"++map clean(take 5 str)))
           (bad_res "?")

readVListPred :: String -> (VSetPred,String)
-- expect VS to begin
readVListPred (c:str) | isSpace c = readVListPred str
readVListPred ('V':'S':str) = readVPredKind str
readVListPred str = (bad_VSetPred str,str)

readVPredKind :: String -> (VSetPred, String)
-- seen VS
-- expect FalseP|Disj|Sub|SubD|TrueP
readVPredKind str
  | before6 == "FalseP" = (VSFalseP,after6)
  | before4 == "Disj"   = read2Preds VSDisj after4
  | before4 == "SubD"   = read2Preds VSSubD after4
  | before3 == "Sub"    = read2Preds VSSub  after3
  | before5 == "TrueP"  = (VSTrueP,after5)
  | otherwise           = (bad_VSetPred "invalid_pred_constructor",str)
  where 
   (before3,after3) = splitAt 3 str
   (before4,after4) = splitAt 4 str
   (before5,after5) = splitAt 5 str
   (before6,after6) = splitAt 6 str

read2Preds :: (VSetExpr -> VSetExpr -> VSetPred) 
          -> String -> (VSetPred,String)
read2Preds make str0 
  = let (set1,str1) = readPar readVListExpr str0
    in case str1 of
         (' ':str1') 
            ->  let (set2,str2) = readPar readVListExpr str1'
                in (make set1 set2,str2)
         _  ->  (bad_VSetPred "missing_space_between_2_sets",str1)
\end{code}


\subsection{Smart Set Predicate constructors}

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


\subsection{Set Predicate Queries}

\begin{code}
vPredVars :: VSetPred -> VarSet
vPredVars (VSDisj vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vPredVars (VSSub  vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vPredVars (VSSubD vse1 vse2)  =  vSetVars vse1 `S.union` vSetVars vse2
vPredVars _                   =  S.empty
\end{code}

\newpage
\subsection{Simplifying Set Predicates}

We can/may encode some standard set-theoretic simplifications here.

In addition, 
we have an interpretation of predicate $S_1 ~rel~S_2$
where $S_1$ represents a set $G$ (usually singleton)
that is an enumeration of variables that denote term free-variables,
while $S_2$ is a general variable set $V$.

\textbf{Note: }
We need to check for each $rel$ that the following holds:
$$(G_1\cup G_2)~rel~V 
  \quad = \quad
  (G_1\cup~rel~V) \land (G_2~rel~V)
$$
\begin{eqnarray*}
   (G_1\cup G_2)~\disj~V 
   \quad = \quad
  (G_1~\disj~V) \land (G_2~\disj~V)
\\ (G_1\cup G_2)~\subseteq~V 
  \quad = \quad
  (G_1~\subseteq~V) \land (G_2~\subseteq~V)
\end{eqnarray*}
Exercise: prove the above.

An issue that arises is how to simplify two such predicates,
where $G_1 = G_2 = G$.
$$ (G~rel_1~V_1) \land (G~rel_2~V_2) \quad = ?$$
This breaks down into two sub-categories:
same predicate ($rel_1=rel_2$),
and different predicate ($rel_1 \neq rel_2$).




\subsubsection{Same Predicate Simplification}

We start with some same-predicate simplification laws,
that reduce a list of predicates with the same relation down to 
a single instance of that relation.
\begin{code}
enumSamePred :: VSetPred -> VSetPred -> VSetPred
enumSamePred (VSDisj g1@(VSEnum gs1) (vs1)) (VSDisj (VSEnum gs2) (vs2))
  | gs1 == gs2  = enumSameDisj g1 vs1 vs2
enumSamePred (VSSub g1@(VSEnum gs1) (vs1)) (VSSub (VSEnum gs2) (vs2))
  | gs1 == gs2  = enumSameSub g1 vs1 vs2
enumSamePred (VSSubD g1@(VSEnum gs1) (vs1)) (VSSubD (VSEnum gs2) (vs2))
  | gs1 == gs2  = enumSameSubD g1 vs1 vs2
enumSamePred VSFalseP _ = VSFalseP
enumSamePred _ VSFalseP = VSFalseP
enumSamePred VSTrueP vsp2 = vsp2
enumSamePred vsp1 VSTrueP = vsp1
enumSamePred vsp1 vsp2 = VSFalseP -- shouldn't happen if used properly
\end{code}
\begin{eqnarray*}
   G \disj D_1 \land G \disj D_2
   &=& G \disj (D_1 \cup D_2)
\\ G \subseteq C_1 \land G \subseteq C_2
   &=& G \subseteq (C_1 \cap C_2)
\\ G \subseteq_d Cd_1 \land G \subseteq_d Cd_2 
   &=& G \subseteq_d (Cd_1 \cap Cd_2)
\end{eqnarray*}
\begin{code}
enumSameDisj :: VSetExpr -> VSetExpr -> VSetExpr -> VSetPred
enumSameDisj gs vs1 vs2 = VSDisj gs (vs1 `VSUnion` vs2)
enumSameSub :: VSetExpr -> VSetExpr -> VSetExpr -> VSetPred
enumSameSub gs vs1 vs2 = VSSub gs (vs1 `VSIntsct` vs2)
enumSameSubD :: VSetExpr -> VSetExpr -> VSetExpr -> VSetPred
enumSameSubD gs vs1 vs2 = VSSubD gs (vs1 `VSIntsct` vs2)
\end{code}


\subsubsection{Different Predicate Simplification}

We continue with the following four different-predicate normalising laws,
that combine and simplify relations as much as possible.
\begin{eqnarray*}
   G \disj D \land G \subseteq C 
   &=& G \disj (D \setminus C) \land G \subseteq (C \setminus D)
\\ G \disj D \land G \subseteq_d Cd 
   &=& G \disj (D \setminus Cd) \land G \subseteq_d (Cd \setminus D)
\\ G \subseteq C \land G \subseteq_d Cd 
   &=& G \subseteq_d (C \cap Cd)
\\ G \disj D \land G \subseteq C \land G \subseteq_d Cd 
   &=& G \disj (D \setminus Cd) \land g \subseteq_d (Cd \setminus D)
\end{eqnarray*}


