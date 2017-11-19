\section{Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Variables
 ( VarClass
 , pattern ObsV, pattern ExprV, pattern PredV
 , VarWhen
 , pattern Static, pattern Textual
 , pattern Before, pattern During, pattern After
 , isDuring
 , Variable
 , pattern Vbl
 , pattern ObsVar, pattern ExprVar, pattern PredVar
 , pattern PreVar, pattern MidVar, pattern PostVar
 , pattern ScriptVar
 , pattern PreCond, pattern PostCond
 , pattern PreExpr, pattern PostExpr
 , isPreVar, isObsVar, isExprVar, isPredVar
 , whatVar, timeVar
 , ListVar
 , pattern LVbl
 , pattern ObsLVar, pattern VarLVar, pattern ExprLVar, pattern PredLVar
 , pattern PreVars, pattern PostVars, pattern MidVars
 , pattern ScriptVars
 , pattern PreExprs, pattern PrePreds
 , isPreListVar, isObsLVar, isExprLVar, isPredLVar
 , whatLVar, timeLVar
 , GenVar, pattern StdVar, pattern LstVar
 , isStdV, isLstV
 , isPreGenVar, isObsGVar, isExprGVar, isPredGVar
 , whatGVar, timeGVar
 , VarList
 , stdVarsOf, listVarsOf
 , VarSet, stdVarSetOf, listVarSetOf
 , isPreVarSet
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
import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{Variable Introduction}


We want to implement a range of variables
that can stand for behaviour observations, and arbitrary terms.
We also want to support the notion of list-variables that denote lists of variables.

We start with a table (Fig. \ref{fig:utp-vv}) that identifies
the variety of variables we expect to support.

\begin{figure}
  \begin{center}
    \begin{tabular}{l|c|cc}
       \multicolumn{1}{r|}{class}
       & Obs
       & \multicolumn{2}{c}{Term}
    \\ & & &
    \\ timing & Var & Expr & Pred
    \\\hline
       Static/Rel & $g$ & $E$ & $P$
    \\ ~~Text & \texttt{x} & \texttt{e} & \texttt{p}
    \\ Before & $x$ & $e$ & $p$
    \\ During & $x_m$ & $e_m$ & $p_m$
    \\ After & $x'$ & $e'$ & $p'$
    \end{tabular}
  \end{center}
  \caption{UTP variable varieties}
  \label{fig:utp-vv}
\end{figure}

Variables fall into two broad classes:
\begin{description}
  \item[Obs]
    Variables that represent some aspect of an observation
    that might be made of a program or its behaviour.
  \item[Term]
    Variables that stand for terms,
    which can themselves be categorised as either expressions (Expr)
    or predicates (Pred).
\end{description}
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

\newpage
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
    Also included here are (Text)
    variables that (statically) denote themselves if observational (\texttt{x}),
    or expression (\texttt{e}) and predicate (\texttt{p}) texts, otherwise.
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
    These are typically required when defining
    sequential composition.
\end{description}
\begin{code}
data VarWhen -- Variable role
  = WS -- Static
  | WT -- Text
  | WB -- Before (pre)
  | WD String -- During (intermediate)
  | WA -- After (post)
  deriving (Eq, Ord, Show, Read)

pattern Static = WS
pattern Textual = WT
pattern Before = WB
pattern During n = WD n
pattern After  = WA

isDuring (During _)  =  True
isDuring _           =  False
\end{code}

\subsubsection{More about variables}

\paragraph{Observational Variables}
Observational variables record visible events/changes/values/histories
associated with program behaviour.
Observation or Term variables with a temporality of Text, Before, During or After,
(\textit{e.g., } $\texttt{x},x,x_m,x'$), are linked by their common identifier
(\textit{e.g.,} \textsl{x}).
Static observational variables are also used for general predicate calculus
purposes.

\paragraph{Term Variables}
Term variables denote terms, either arbitrary or pre-determined in some way.
If a term contains only observable variables of the same temporality,
then it can be deoted by a term variable of that temporality.
Term variables are sub-classified by those that denote expressions (Expr)
and those that denote predicates (Pred).
There are no term variables that can denote both expressions and predicates.
Static term variables may denote an term of the same sub-classification,
with any temporality attribute.

\paragraph{Variables qua Variables}
Finally, for observational variables only,
we have the notion of a (Text) variable standing for itself (\texttt{x}),
rather than its value at some point in time.
This is very important for the definition
of language constructs involving variables in an essential way,
such as assignment.
In a sense, these variables are static.

\subsection{Variable Definition}

A variable is a triple: identifier, class, and temporality/text
\begin{code}
newtype Variable  = VR (Identifier, VarClass, VarWhen)
 deriving (Eq,Ord,Show,Read)

pattern Vbl idnt cls whn = VR (idnt, cls, whn)

pattern ObsVar  i vw = VR (i, VO, vw)
pattern ExprVar i vw = VR (i, VE, vw)
pattern PredVar i vw = VR (i, VP, vw)
\end{code}

We also have some pre-wrapped patterns for common cases:
\begin{code}
pattern PreVar    i    = VR (i, VO, WB)
pattern PostVar   i    = VR (i, VO, WA)
pattern MidVar    i n  = VR (i, VO, (WD n))
pattern ScriptVar i    = VR (i, VO, WT)
pattern PreCond   i    = VR (i, VP, WB)
pattern PostCond  i    = VR (i, VP, WA)
pattern PreExpr   i    = VR (i, VE, WB)
pattern PostExpr  i    = VR (i, VE, WA)
\end{code}

Some variable predicates/functions:
\begin{code}
isPreVar :: Variable -> Bool
isPreVar  (VR (_, _, WB))  =  True
isPreVar  _                     =  False
isObsVar  (VR (_, vw, _))   =  vw == VO
isExprVar (VR (_, vw, _))  =  vw == VE
isPredVar (VR (_, vw, _))  =  vw == VP

whatVar (VR (_,vc,_))  =  vc
timeVar (VR (_,_,vt))  =  vt

\end{code}

\newpage
\subsection{List Variables}

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
of a list of identifiers, corresponding to variable `roots'

\begin{code}
newtype ListVar = LV (Variable, [Identifier])
 deriving (Eq, Ord, Show, Read)

pattern LVbl v is = LV (v,is)

pattern ObsLVar  k i is = LV (VR (i,VO,k),is)
pattern VarLVar  i is = LV (VR (i,VO,WT),is)
pattern ExprLVar k i is = LV (VR (i,VE,k),is)
pattern PredLVar k i is = LV (VR (i,VP,k),is)
\end{code}

Pre-wrapped patterns:
\begin{code}
pattern PreVars  i    =  LV (VR (i,VO,WB),[])
pattern PostVars i    =  LV (VR (i,VO,WA),[])
pattern MidVars  i n  =  LV (VR (i,VO,(WD n)),[])
pattern ScriptVars i  =  LV (VR (i,VO,WT),[])
pattern PreExprs i    =  LV (VR (i,VE,WB),[])
pattern PrePreds i    =  LV (VR (i,VP,WB),[])
\end{code}

Useful predicates/functiond:
\begin{code}
isPreListVar :: ListVar -> Bool
isPreListVar (PreVars _)  = True
isPreListVar (PreExprs _) = True
isPreListVar (PrePreds _) = True
isPreListVar _            = False

isObsLVar  (LV (v,_)) = isObsVar v
isExprLVar (LV (v,_)) = isExprVar v
isPredLVar (LV (v,_)) = isPredVar v

whatLVar (LV (v,_)) = whatVar v
timeLVar (LV (v,_)) = timeVar v
\end{code}

\newpage
\subsection{Variable Lists}

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

type VarList = [GenVar]
\end{code}

Some useful predicates/functions:
\begin{code}
isStdV (StdVar _)  =  True ;  isStdV _  =  False
isLstV (LstVar _)  =  True ;  isLstV _  =  False

stdVarsOf :: VarList -> [Variable]
stdVarsOf []             =  []
stdVarsOf ((GV sv:gvs))  =  sv:stdVarsOf gvs
stdVarsOf (_:gvs)        =  stdVarsOf gvs

listVarsOf :: VarList -> [ListVar]
listVarsOf []             =  []
listVarsOf ((GL lv:gvs))  =  lv:listVarsOf gvs
listVarsOf (_:gvs)        =  listVarsOf gvs

isPreGenVar :: GenVar -> Bool
isPreGenVar (StdVar v) = isPreVar v
isPreGenVar (LstVar lv) = isPreListVar lv

isObsGVar  (GV v)   =  isObsVar v
isObsGVar  (GL lv)  =  isObsLVar lv
isExprGVar (GV v)   =  isExprVar v
isExprGVar (GL lv)  =  isExprLVar lv
isPredGVar (GV v)   =  isPredVar v
isPredGVar (GL lv)  =  isPredLVar lv

whatGVar (GV v)   =  whatVar v
whatGVar (GL lv)  =  whatLVar lv
timeGVar (GV v)   =  timeVar v
timeGVar (GL lv)  =  timeLVar lv
\end{code}

\newpage
\subsection{Variable Sets}

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

\end{code}


\newpage

\subsection{Exported Test Group}
\begin{code}
int_tst_Variables :: [TF.Test]
int_tst_Variables
 = [ testGroup "\nVariables Internal"
     [ testCase "No tests currently defined" (1+1 @?= 2)
     ]
   ]
\end{code}
