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
  readsPrec _ str = [readVListExpr $ pdbg "READVLIST.STR" str]

bad_res msg = vsSngl $ StdVar $ PredVar (jId msg) Static
bad_VSetExpr str = bad_res ("BAD_VSetExpr_"++map clean(take 5 $ pdbg "BVSE.str" str))
clean c = if isIdContChar c then c else '?'
bad_NYI str = bad_res (str++"_NYI")

readVListExpr :: String -> (VSetExpr,String)
-- expect VS to begin
readVListExpr (c:str) | isSpace c = readVListExpr str
readVListExpr ('V':'S':str) = readVKind str
readVListExpr str = (bad_VSetExpr str,str)

readVKind :: String -> (VSetExpr, String)
-- seen VS
-- expect Enum|Union|Intsct|Minus
readVKind str
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

data VSetPred
  =  VSFalseP -- yes, we need this
  |  VSDisj  VSetExpr VSetExpr  
  |  VSSub   VSetExpr VSetExpr 
  |  VSSubD  VSetExpr VSetExpr  -- limited to dynamic vars
  |  VSTrueP
  deriving (Eq,Ord,Show,Read)
\end{code}

\section{Smart Set Expression Constructors}

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

\section{Set Expression Queries}

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





