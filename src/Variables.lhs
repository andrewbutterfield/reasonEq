\section{Variables}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Variables ( VarWhat
           , pattern ObsV, pattern VarV, pattern ExprV, pattern PredV
           , VarWhen
           , pattern Before, pattern During, pattern After
           , isDuring
           , VarTime
           , pattern Static, pattern Dynamic
           , Variable
           , pattern Vbl
           , pattern ObsVar, pattern VarVar, pattern ExprVar, pattern PredVar
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

Variables have a root identifier,
can represent either obervations,expressions or predicates,
and can be static or dynamic.
A dynamic variable has to be classified regarding
when in program execution history it applies: before, during or after.

Variables can be classified into those that:
\begin{itemize}
  \item
     track a single observable aspect of the behaviour as the program
    runs,
  \item
    denote an arbitrary variable, as when defining a language construct,
  \item
    denote arbitrary expressions whose values depend on dynamic observables,
    or
  \item
    denote arbitrary predicates whose truth value depend on dynamic observables.
\end{itemize}
\begin{code}
data VarWhat -- Classification
  = VO -- Observation
  | VV -- Variable
  | VE -- Expression
  | VP -- Predicate
  deriving (Eq, Ord, Show, Read)

pattern ObsV  = VO
pattern VarV  = VV
pattern ExprV = VE
pattern PredV = VP
\end{code}


Variables are either:
\begin{description}
  \item[Static]
    that capture information, or define terms, that do not change during
    the lifetime of a program.
  \item[Dynamic]
    that represent behaviour
    with observations that change as the program runs.
    These can have added `decorations' that limit their scope
    to pre, post, and intermediate states of execution.
\end{description}


We start by defining the various ``timings'' for dynamic variables
\begin{code}
data VarWhen -- Variable role
  = WB -- Before (pre)
  | WD String -- During (intermediate)
  | WA -- After (post)
  deriving (Eq, Ord, Show, Read)

pattern Before = WB
pattern During n = WD n
pattern After  = WA
\end{code}

Variables may have a particular interpretation
with respect to time, (``temporality''),
being either static (independent of time),
or dynamic, distinguishing between before, durimg or after
some behaviour of interest.
\begin{code}
data VarTime
  = TS -- Static
  | TD VarWhen -- Dynamic
  deriving (Eq, Ord, Show, Read)

pattern Static = TS
pattern Dynamic w = TD w

isDuring (Dynamic (During _)) = True
isDuring _                    = False
\end{code}

A variable is a triple: identifier, what, and time
\begin{code}
newtype Variable  = VR (Identifier, VarWhat, VarTime)
 deriving (Eq,Ord,Show,Read)

pattern Vbl  i wt kd = VR (i, wt, kd)

pattern ObsVar  i k = Vbl i VO k
pattern VarVar  i k = Vbl i VV k
pattern ExprVar i k = VR (i, VE, k)
pattern PredVar i k = VR (i, VP, k)
\end{code}

We also have some pre-wrapped patterns for common cases:
\begin{code}
pattern PreVar   i    = VR (i, VO, (TD WB))
pattern PostVar  i    = VR (i, VO, (TD WA))
pattern MidVar   i n  = VR (i, VO, (TD (WD n)))
pattern ScriptVar i   = VR (i, VV, TS)
pattern PreCond  i    = VR (i, VP, (TD WB))
pattern PostCond i    = VR (i, VP, (TD WA))
pattern PreExpr  i    = VR (i, VE, (TD WB))
pattern PostExpr i    = VR (i, VE, (TD WA))
\end{code}

Some variable predicates/functions:
\begin{code}
isPreVar :: Variable -> Bool
isPreVar (VR (_, _, (TD WB)))  =  True
isPreVar _                     =  False
isObsVar (VR (_, vw, _))   =  vw == VO
isExprVar (VR (_, vw, _))  =  vw == VE
isPredVar (VR (_, vw, _))  =  vw == VP

whatVar (VR (_, vw, _))  =  vw
timeVar (VR (_, _, vt))  =  vt
\end{code}

\subsection{Identifier and Variable test values}
\begin{code}
i_a = fromJust $ ident "a"
i_b = fromJust $ ident "b"
i_e = fromJust $ ident "e"
i_f = fromJust $ ident "f"
i_v = fromJust $ ident "v"
i_P = fromJust $ ident "P"
i_Q = fromJust $ ident "Q"

v_a =  PreVar    $ i_a
v_b =  PreVar    $ i_b
v_v =  ScriptVar $ i_v
v_a' = PostVar   $ i_a
v_b' = PostVar   $ i_b

v_e  = PreExpr  $ i_e
v_f  = PreExpr  $ i_f
v_e' = PostExpr $ i_e
v_f' = PostExpr $ i_f

v_P  = PreCond  i_P
v_Q' = PostCond i_Q
\end{code}

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
pattern VarLVar  k i is = LV (VR (i,VV,k),is)
pattern ExprLVar k i is = LV (VR (i,VE,k),is)
pattern PredLVar k i is = LV (VR (i,VP,k),is)
\end{code}

Pre-wrapped patterns:
\begin{code}
pattern PreVars  i    =  LV (VR (i,VO,(TD WB)),[])
pattern PostVars i    =  LV (VR (i,VO,(TD WA)),[])
pattern MidVars  i n  =  LV (VR (i,VO,(TD (WD n))),[])
pattern ScriptVars i  =  LV (VR (i,VV,(TD WB)),[])
pattern PreExprs i    =  LV (VR (i,VE,(TD WB)),[])
pattern PrePreds i    =  LV (VR (i,VP,(TD WB)),[])
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

\subsection{List Variable test values}
\begin{code}
lva = ObsLVar  (Dynamic Before) (i_a) []
lvb = ObsLVar  (Dynamic After)  (i_b) []
lve = ExprLVar (Dynamic Before) (i_e) []
lvf = ExprLVar (Dynamic Before) (i_f) []
\end{code}

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

Test values:
\begin{code}
gv_a =  StdVar v_a
gv_b =  StdVar v_b
gv_v =  StdVar v_v
gv_a' = StdVar v_a'
gv_b' = StdVar v_b'
\end{code}


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

\subsection{Variable Set test values}
\begin{code}
s0   = S.fromList [] :: VarSet
sa   = S.fromList [gv_a]
sa'  = S.fromList [gv_a']
sb   = S.fromList [gv_b]
sab  = S.fromList [gv_a,gv_b]
saa' = S.fromList [gv_a,gv_a']
sab' = S.fromList [gv_a,gv_b']
sbb' = S.fromList [gv_b,gv_b']
\end{code}



\newpage

\subsection{Exported Test Group}
\begin{code}
int_tst_Variables :: [TF.Test]
int_tst_Variables
 = [ testGroup "\nVariables Internal"
     [ testCase "1+1=2" (1+1 @?= 2)
     ]
   ]
\end{code}
