\chapter{Variables}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Variables
 ( VarClass
 , pattern ObsV, pattern ExprV, pattern PredV
 , Subscript, VarWhen
 , pattern Static
 , pattern Before, pattern During, pattern After, pattern Textual
 , isDynamic, isDuring, theSubscript, whenMatches
 , Variable
 , pattern Vbl
 , varClass, varWhen
 , whenVarMatches
 , pattern ObsVar, pattern ExprVar, pattern PredVar
 , pattern StaticVar, pattern PreVar, pattern MidVar, pattern PostVar
 , pattern ScriptVar
 , pattern PreCond, pattern PostCond -- tests only ?
 , pattern PreExpr, pattern PostExpr, pattern MidExpr -- all tests only?
 , isPreVar, isObsVar
 , isPredVar, dynVarEq
 , whatVar, timeVar
 , ListVar
 , pattern LVbl
 , lvarClass, lvarWhen
 , pattern ObsLVar, pattern VarLVar, pattern ExprLVar, pattern PredLVar -- tests only?
 , pattern StaticVars -- tests only
 , pattern PreVars, pattern PostVars, pattern MidVars
 , pattern PreExprs, pattern PrePreds -- tests only
 , whatLVar, timeLVar
 , less, makeVars
 , GenVar, pattern StdVar, pattern LstVar
 , isStdV, isLstV, theStdVar, theLstVar
 , getIdClass, sameIdClass
 , gvarClass, gvarWhen, isDynGVar
 , isObsGVar, isExprGVar, isPredGVar, isStdObs
 , dynGVarEq
 , whatGVar, timeGVar
 , setVarWhen, setLVarWhen, setGVarWhen
 , VarList
 , varId, varOf, idsOf, stdVarsOf, listVarsOf, allStdObsL
 , VarSet, stdVarSetOf, listVarSetOf, allStdObsS
 , liftLess
 , dnWhen, dnVar, dnLVar, dnGVar
 , unVar, unLVar, unGVar
 , fI, fIn, fVar, fLVar, fGVar
 , isFloating, isFloatingV, isFloatingLV, isFloatingGVar
 , sinkId, sinkV, sinkLV, sinkGV
 , int_tst_Variables
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

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}


\newpage
\section{Variable Introduction}


We want to implement a range of variables
that can stand for behaviour observations, and arbitrary terms.
We also want to support the notion of list-variables that denote lists of variables.

We start with a table (Fig. \ref{fig:utp-vv}) that identifies
the variety of variables we expect to support.

\begin{figure}[h]
  \begin{center}
    \begin{tabular}{l|c|cc}
       \multicolumn{1}{r|}{class}
       & Obs
       & \multicolumn{2}{c}{Term}
    \\ & & &
    \\ timing & Var & Expr & Pred
    \\\hline
       Static/Rel & $g$ & $E$ & $P$
    \\ Before & $x$ & $e$ & $p$
    \\ During & $x_m$ & $e_m$ & $p_m$
    \\ After & $x'$ & $e'$ & $p'$
    \\ Textual & \texttt{x} & \texttt{e} & \texttt{p}
    \end{tabular}
  \end{center}
  \caption{UTP variable varieties}
  \label{fig:utp-vv}
\end{figure}

Variables fall into two broad classes:
\begin{description}
  \item[Obs]
    Variables ($x,v,\dots$)that represent some aspect of an observation
    that might be made of a program or its behaviour.
  \item[Term]
    Variables that stand for terms,
    which can themselves be categorised as 
    either expressions (Expr, $e,f,\dots$)
    or predicates (Pred, $P,Q,\dots$).
\end{description}
The key feature that distinguishes observation variables from term variables
has to do with free-variables. 
An observation variable can be determined to be free or bound
in a containing term in the usual way.
A term variable is different as in general it is associated with
a set of free variables and another set of bound variables,
based on whatever term ``value'' it has.
The best we can do in general is say (for example) that:
$\fv(x = e \land P) = \setof x \cup \fv(e) \cup \fv(P)$.
In particular, $\fv(x = e \land P)$ cannot be $\setof{x,e,P}$.
\begin{code}
data VarClass -- Classification
  = VO -- Observation
  | VE -- Expression
  | VP -- Predicate
  deriving (Eq, Ord, Show, Read)

pattern ObsV  = VO
pattern ExprV = VE
pattern PredV = VP
\end{code}

Within these classes, we can also classify variables further
in terms of their ``temporality''.
We describe behaviour in terms of relations between ``before''
and ``after'' observations over some appropriate time interval.
\begin{description}
  \item[Static/Rel]
    variables that represent a value ($g$), or relationship
    between before- and after-values ($E$,$P$),
    that does not change
    over the lifetime of a program.
  \item[Before]
    variables that record the value of observations
    at the start of the time interval under consideration ($x$),
    or terms defined over starting values ($e,p$).
  \item[After]
    variables that record the value of observations
    at the end of the time interval under consideration ($x'$),
    or terms defined over final values ($e',p'$).
  \item[During]
    variables used to record the value of observations
    at intermediate points within the time interval under consideration ($x_m$),
    or terms defined at such in-between states ($e_m,p_m$.).
    These are normally only required when dealing with
    sequential composition.
  \item[Textual]
    variables that denote themselves if observational (\texttt{x}),
    or expression (\texttt{e}) and predicate (\texttt{p}) texts, otherwise.
\end{description}
\begin{code}
type Subscript = String

data VarWhen -- Variable role
  = WS            --  Static
  | WB            --  Before (pre)
  | WD Subscript  --  During (intermediate)
  | WA            --  After (post)
  | WT            --  Textual
  deriving (Eq, Ord, Show, Read)

pattern Static    =  WS
pattern Before    =  WB
pattern During n  =  WD n
pattern After     =  WA
pattern Textual   =  WT
\end{code}

We consider before, during and after variables as being ``dynamic'' ($\isdyn$).
These sometimes need special treatment.
\begin{code}
isDynamic :: VarWhen -> Bool
isDynamic Static   =  False
isDynamic Textual  =  False
isDynamic _        =  True
isDuring :: VarWhen -> Bool
isDuring (During _)  =  True
isDuring _           =  False
theSubscript :: VarWhen -> Subscript
theSubscript (During s) = s
\end{code}

For matching, 
we have restrictions on the temporalities of candidate and pattern variables.
Basically static pattern variables match anything,
while dynamic pattern variables can only match candidates 
with the same temporality, modulo the ``during'' index.
\begin{code}
whenMatches :: VarWhen -> VarWhen -> Bool  -- candidate, pattern
whenMatches _          Static      =  True
whenMatches Textual    Textual     =  True
whenMatches Before     Before      =  True
whenMatches (During _) (During _)  =  True
whenMatches After      After       =  True
whenMatches _          _           =  False
\end{code}


\subsection{More about variables}

\subsubsection{Observational Variables}
Observational variables record visible events/changes/values/histories
associated with program behaviour.
Observation or Term variables with a temporality of Text, Before, During or After,
(\textit{e.g., } $\texttt{x},x,x_m,x'$), are linked by their common identifier
(\textit{e.g.,} \textsl{x}).
Static observational variables are also used for general predicate calculus
purposes.

\subsubsection{Term Variables}
Term variables denote terms, either arbitrary or pre-determined in some way.
If a term contains only observable variables of the same temporality,
then it can be denoted by a term variable of that temporality.
Term variables are sub-classified by those that denote expressions (Expr)
and those that denote predicates (Pred).
Predicates are boolean valued expressions, so there is an overlap.
Static term variables may denote an term of the same sub-classification,
with any temporality attribute.

\subsubsection{Variables qua Variables}
Finally, for observational variables only,
we have the notion of a (Text) variable standing for itself (\texttt{x}),
rather than its value at some point in time.
This is very important for the definition
of language constructs involving variables in an essential way,
such as assignment.
In a sense, these variables are static.

\section{Variable Definition}

A variable is a triple: identifier, class, and temporality/text
\begin{code}
newtype Variable  = VR (Identifier, VarClass, VarWhen)
 deriving (Eq,Ord,Show,Read)

pattern Vbl idnt cls whn = VR (idnt, cls, whn)
varClass (Vbl _ vc _)  =  vc
varWhen  (Vbl _ _ vw)  =  vw

pattern ObsVar  i vw = VR (i, VO, vw)
pattern ExprVar i vw = VR (i, VE, vw)
pattern PredVar i vw = VR (i, VP, vw)
\end{code}

We also have some pre-wrapped patterns for common cases:
\begin{code}
pattern StaticVar i    = VR (i, VO, WS)
pattern PreVar    i    = VR (i, VO, WB)
pattern PostVar   i    = VR (i, VO, WA)
pattern MidVar    i n  = VR (i, VO, (WD n))
pattern ScriptVar i    = VR (i, VO, WT)
pattern PreCond   i    = VR (i, VP, WB)
pattern PostCond  i    = VR (i, VP, WA)
pattern MidCond   i n  = VR (i, VP, (WD n))
pattern PreExpr   i    = VR (i, VE, WB)
pattern PostExpr  i    = VR (i, VE, WA)
pattern MidExpr   i n  = VR (i, VE, (WD n))
\end{code}

Some variable predicates/functions:
\begin{code}
isPreVar :: Variable -> Bool
isPreVar  (VR (_, _, WB))  =  True
isPreVar  _                =  False
isObsVar  (VR (_, vw, _))  =  vw == VO
isExprVar (VR (_, vw, _))  =  vw == VE
isPredVar (VR (_, vw, _))  =  vw == VP

whatVar (VR (_,vc,_))  =  vc
timeVar (VR (_,_,vt))  =  vt
\end{code}


\begin{code}
whenVarMatches :: Variable -> Variable -> Bool
whenVarMatches (Vbl _ _ vkC) (Vbl _ _ vkP) = whenMatches vkC vkP
\end{code}


Sometimes we want to compare two variables, while ignoring their temporality.
Such a comparison can fail, or succeed, returning the temporality of the 2nd variable.
\begin{code}
dynVarEq :: MonadFail m => Variable -> Variable -> m VarWhen
(VR (i1,c1,_)) `dynVarEq` (VR (i2,c2,w2))
  | i1 == i2 && c1 == c2  =  return w2
  | otherwise             =  fail "dynVarEq: fails"
\end{code}

\newpage
\section{List Variables}

In places where list of variables occur,
it is very useful to have (single) variables
that are intended to represent such lists.
We call these list-variables,
and they generally can take similar decorations as dynamic variables.
Such lists occur in binders, substitutions and iterated terms.

We also need to introduce the idea of lists of variables,
for use in binding constructs,
which may themselves contain special variables
that denote lists of variables.
We define a list-variable as a specially marked variable with the addition
of two lists of identifiers,
corresponding to ``subtracted'' variable  and list-variable `roots' respectively.

\begin{code}
newtype ListVar = LV (Variable, [Identifier], [Identifier])
 deriving (Eq, Ord, Show, Read)

pattern LVbl v is js = LV (v,is,js)
lvarClass (LVbl v _ _)  =  varClass v
lvarWhen  (LVbl v _ _)  =  varWhen  v

pattern ObsLVar  k i is js = LV (VR (i,VO,k), is,js)
pattern VarLVar    i is js = LV (VR (i,VO,WT),is,js)
pattern ExprLVar k i is js = LV (VR (i,VE,k), is,js)
pattern PredLVar k i is js = LV (VR (i,VP,k), is,js)
\end{code}

Pre-wrapped patterns:
\begin{code}
pattern StaticVars i    =  LV (VR (i,VO,WS),    [],[])
pattern PreVars    i    =  LV (VR (i,VO,WB),    [],[])
pattern PostVars   i    =  LV (VR (i,VO,WA),    [],[])
pattern MidVars    i n  =  LV (VR (i,VO,(WD n)),[],[])
pattern ScriptVars i    =  LV (VR (i,VO,WT),    [],[])
pattern PreExprs   i    =  LV (VR (i,VE,WB),    [],[])
pattern PrePreds   i    =  LV (VR (i,VP,WB),    [],[])
\end{code}

Useful predicates/functions:
\begin{code}
isPreListVar :: ListVar -> Bool
isPreListVar (PreVars _)  = True
isPreListVar (PreExprs _) = True
isPreListVar (PrePreds _) = True
isPreListVar _            = False

isObsLVar  (LV (v,_,_)) = isObsVar v
isExprLVar (LV (v,_,_)) = isExprVar v
isPredLVar (LV (v,_,_)) = isPredVar v

whatLVar (LV (v,_,_)) = whatVar v
timeLVar (LV (v,_,_)) = timeVar v
\end{code}

Sometimes we also want to compare two list variables, 
while ignoring their temporality.
Such a comparison can fail, or succeed, returning the temporality of the 2nd variable.
\begin{code}
dynLVarEq :: MonadFail m => ListVar -> ListVar -> m VarWhen
(LV (v1,is1,js1)) `dynLVarEq` (LV (v2,is2,js2))
  | is1 == is2 && js1 == js2  =  v1 `dynVarEq` v2
  | otherwise                 =  fail "dynLVarEq: fails"
\end{code}


We provide a constructor to subtract (more) variables,
which sorts them, as they are considered to be sets.
\begin{code}
less :: ListVar -> ([Identifier],[Identifier]) -> ListVar
(LVbl v is ij) `less` (iv,il)
 = LVbl v (nub $ sort (is++iv)) (nub $ sort (is++il))
\end{code}
We also provide ways to get the subtracted variables back out:
\begin{code}
lessVars :: ListVar -> ([Variable],[ListVar])
lessVars (LV (VR (vi,vc,vw),vis,lvis)) = makeVars vc vw vis lvis

makeVars :: VarClass -> VarWhen -> [Identifier] -> [Identifier]
         -> ([Variable],[ListVar])
makeVars vc vw vis lvis
  = ( map (mkv vc vw) vis, map (mklv vc vw) lvis )
  where
    mkv vc vw vi    =  VR (vi,vc,vw)
    mklv vc vw lvi  =  LV (mkv vc vw lvi, [], [])
\end{code}

\newpage
\section{Variable Lists}

A variable-list is composed in general of a mix of normal variables
and list-variables.
We gather these into a `general' variable type
\begin{code}
data GenVar
 = GV Variable -- regular variable
 | GL ListVar  -- variable denoting a list of variables
 deriving (Eq, Ord, Show, Read)

pattern StdVar v = GV v
pattern LstVar lv = GL lv

gvarClass (StdVar v)   =  varClass  v
gvarClass (LstVar lv)  =  lvarClass lv
gvarWhen  (StdVar v)   =  varWhen  v
gvarWhen  (LstVar lv)  =  lvarWhen lv
isDynGVar = isDynamic . gvarWhen
\end{code}

Some useful predicates/functions:
\begin{code}
isStdV (StdVar _)  =  True ;  isStdV _  =  False
isLstV (LstVar _)  =  True ;  isLstV _  =  False


theStdVar :: GenVar -> Variable
theStdVar (GV v) = v ; theStdVar _ = error "theStdVar: applied to LstVar"

theLstVar :: GenVar -> ListVar
theLstVar (GL lv) = lv ; theLstVar _ = error "theLstVar: applied to StdVar"

varId :: Variable -> Identifier
varId (VR(i,_,_)) = i

varOf :: ListVar -> Variable
varOf (LV (v,_,_)) = v

getIdClass :: GenVar -> (Identifier, VarClass)
getIdClass (StdVar (Vbl i vc _))             =  (i,vc)
getIdClass (LstVar (LVbl (Vbl i vc _) _ _))  =  (i,vc)
-- NOTE: this forgets the Std/Lst distinction !!!

sameIdClass gv1@(StdVar _) gv2@(StdVar _)  =  getIdClass gv1 == getIdClass gv2
sameIdClass gv1@(LstVar _) gv2@(LstVar _)  =  getIdClass gv1 == getIdClass gv2
sameIdClass _ _                            =  False

isPreGenVar :: GenVar -> Bool
isPreGenVar (StdVar v) = isPreVar v
isPreGenVar (LstVar lv) = isPreListVar lv

isObsGVar  (GV v)   =  isObsVar v
isObsGVar  (GL lv)  =  isObsLVar lv
isExprGVar (GV v)   =  isExprVar v
isExprGVar (GL lv)  =  isExprLVar lv
isPredGVar (GV v)   =  isPredVar v
isPredGVar (GL lv)  =  isPredLVar lv

isStdObs gv = isStdV gv && isObsGVar gv


whatGVar (GV v)   =  whatVar v
whatGVar (GL lv)  =  whatLVar lv
timeGVar (GV v)   =  timeVar v
timeGVar (GL lv)  =  timeLVar lv
\end{code}

Sometimes we also want to compare two general variables, 
while ignoring their temporality.
Such a comparison can fail, or succeed, returning the temporality of the 2nd variable.
\begin{code}
dynGVarEq :: MonadFail m => GenVar -> GenVar -> m VarWhen
(GV v1)  `dynGVarEq` (GV v2)   =  v1  `dynVarEq`  v2
(GL lv1) `dynGVarEq` (GL lv2)  =  lv1 `dynLVarEq` lv2
_        `dynGVarEq` _         =  fail "dynLVarEq: fails"
\end{code}


Changing temporality:
\begin{code}
setVarWhen :: VarWhen -> Variable -> Variable
setVarWhen vw (Vbl i vc _)  =  Vbl i vc vw

setLVarWhen :: VarWhen -> ListVar -> ListVar
setLVarWhen vw (LVbl v is js)  =  LVbl (setVarWhen vw v) is js

setGVarWhen :: VarWhen -> GenVar -> GenVar
setGVarWhen vw (StdVar v)   =  StdVar $ setVarWhen vw v
setGVarWhen vw (LstVar lv)  =  LstVar $ setLVarWhen vw lv
\end{code}

\newpage
\section{Variable Lists}

\begin{code}
type VarList = [GenVar]

idsOf :: VarList -> ([Identifier],[Identifier])
idsOf vl =  idsOf' [] [] vl
idsOf' si sj [] = (reverse si, reverse sj)
idsOf' si sj ((GV      (VR (i,_,_))      ):vl)  =  idsOf' (i:si) sj vl
idsOf' si sj ((GL (LV ((VR (j,_,_)),_,_))):vl)  =  idsOf' si (j:sj) vl

stdVarsOf :: VarList -> [Variable]
stdVarsOf []             =  []
stdVarsOf ((GV sv:gvs))  =  sv:stdVarsOf gvs
stdVarsOf (_:gvs)        =  stdVarsOf gvs

listVarsOf :: VarList -> [ListVar]
listVarsOf []             =  []
listVarsOf ((GL lv:gvs))  =  lv:listVarsOf gvs
listVarsOf (_:gvs)        =  listVarsOf gvs

allStdObsL :: VarList -> Bool
allStdObsL vl = null (filter (not . isStdObs) vl)
\end{code}

\section{Variable Sets}

We also want variable sets:
\begin{code}
type VarSet = Set GenVar

isPreVarSet :: VarSet -> Bool
isPreVarSet = all isPreGenVar . S.toList
\end{code}

\begin{code}
stdVarSetOf :: VarSet -> Set Variable
stdVarSetOf vs  =  S.map getV $ S.filter isStdV vs where getV (GV v)  = v

listVarSetOf :: VarSet -> Set ListVar
listVarSetOf vs =  S.map getL $ S.filter isLstV vs where getL (GL lv) = lv

allStdObsS :: VarSet -> Bool
allStdObsS vs = S.null (S.filter (not . isStdObs) vs)

\end{code}

Given a list-variable,
we will sometimes want to produce from it,
a variable-list that corresponds to the subtracted identifiers:
\begin{code}
liftLess :: ListVar -> VarList
liftLess (LV (VR (_,vc,vw), is, js))
  = map (GV . mkV) is ++ map (GL . mkL) js
  where
     mkV i = VR (i,vc,vw)
     mkL j = LV (mkV j,[],[])
\end{code}


\newpage

\section{Dynamic Variable Normalisation}

Dynamic normalisation (d.n.):
When we record a dynamic variable in certain circumstances,
we ``normalise'' it by setting its temporality to \texttt{Before}.

\begin{code}
dnWhen Static   =  Static
dnWhen Textual  =  Textual
dnWhen _        =  Before

dnVar :: Variable -> Variable
dnVar v@(Vbl vi vc vw)
  | vw == Static || vw == Textual || vw == Before  =  v
  | otherwise                                      =  Vbl vi vc Before

dnLVar :: ListVar -> ListVar
dnLVar lv@(LVbl (Vbl vi vc vw) is ij)
  | vw==Static || vw==Textual || vw==Before  =  lv
  | otherwise                                =  LVbl (Vbl vi vc Before) is ij

dnGVar :: GenVar -> GenVar
dnGVar (StdVar v)   =  StdVar $ dnVar  v
dnGVar (LstVar lv)  =  LstVar $ dnLVar lv
\end{code}

We also need to ``un-normalise'':
\begin{code}
unVar :: VarWhen -> Variable -> Variable
unVar Static v             =  v
unVar Textual v            =  v
unVar vw     (Vbl i vc _)  =  Vbl i vc vw

unLVar :: VarWhen -> ListVar -> ListVar
unLVar vw (LVbl v is ij) = LVbl (unVar vw v) is ij

unGVar :: VarWhen -> GenVar -> GenVar
unGVar vw (StdVar v)   =  StdVar (unVar vw v)
unGVar vw (LstVar lv)  =  LstVar (unLVar vw lv)
\end{code}


\newpage

\section{Floating Variables}

We want to mark some variables as ``floating'',
to indicate that they haven't been matched,
and so are free to be instantiated by the user in some appropriate fashion.
We do this by prepending their
identifiers with a question-mark: $idn \mapsto ?idn$.
\begin{code}
floatMark  =  '?'
\end{code}

Marking as floating:
\begin{code}
fI  (Identifier i u)    =  fromJust $ uident (floatMark:i) u
fIn (Identifier i u) n  =  fromJust $ uident (floatMark:i) (u+n)
fVar (Vbl i c w)        =  Vbl (fI i) c w
fLVar (LVbl v is js)    =  LVbl (fVar v) is js
fGVar (StdVar v)        =  StdVar $ fVar v
fGVar (LstVar v)        =  LstVar $ fLVar v
\end{code}

Checking to see if floating:
\begin{code}
isFloating (Identifier i u)  =  take 1 i == [floatMark]
isFloatingV (Vbl i _ _)      =  isFloating i
isFloatingLV (LVbl v _ _)    =  isFloatingV v
isFloatingGVar (StdVar v)    =  isFloatingV v
isFloatingGVar (LstVar lv)   =  isFloatingLV lv
\end{code}

Sinking:
\begin{code}
sinkId (Identifier (c:cs) u)
  | c == floatMark     =  fromJust $ uident cs u
sinkId i               =  i
sinkV (Vbl i c w)      =  Vbl (sinkId i) c w
sinkLV (LVbl v is js)  =  LVbl (sinkV v) is js
sinkGV (StdVar v)      =  StdVar $ sinkV v
sinkGV (LstVar v)      =  LstVar $ sinkLV v
\end{code}



\newpage

\section{Exported Test Group}
\begin{code}
int_tst_Variables :: [TF.Test]
int_tst_Variables
 = [ testGroup "\nVariables Internal"
     [ testCase "No tests currently defined" (1+1 @?= 2)
     ]
   ]
\end{code}
