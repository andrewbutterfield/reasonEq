\section{Binding}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017-22

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Binding
( VarBind, pattern BindVar, pattern BindTerm
, LVarOrTerm
, injLV, injTM,lvOf, tmOf
, lvsOf, tmsOf, lvtmSplit
, LstVarBind, ListVarKey, pattern BindList, pattern BindSet, pattern BindTLVs
, Binding
, emptyBinding
, mergeBindings
, bindVarToVar, bindVarsToVars, bindVarToSelf, bindVarsToSelves
, bindVarToTerm
, bindLVarToVList
, bindLVarToVSet, overrideLVarToVSet
, bindLVarToSSelf, bindLVarsToSSelves, bindLVarSTuples
, bindLVarToTList
, bindLVarSubstRepl
, bindGVarToGVar
, bindGVarToVList
, lookupVarBind
, lookupLstBind
, bindLVarsToNull, bindLVarsToEmpty
, mappedVars
, findUnboundVars, bindKnown
, termLVarPairings, mkEquivClasses
, mkFloatingBinding, bindFloating
, generateFreshVars
, isBijectiveBinding
, onlyTrivialQuantifiers
, dumpBinding
, patchVarBind, patchVarListBind
, int_tst_Binding
) where
import Data.Maybe (fromJust,catMaybes)
import Data.Either
import Data.List (nub,union,(\\),intersect,partition)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

import YesBut
import Utilities
import LexBase
import Variables
import AST
import VarData

import Debugger
\end{code}

\subsection{Introduction}

Bindings are the result of matching,
mapping pattern variables to corresponding candidate variables or terms.
From the outside a binding has two mappings:
\begin{itemize}
  \item \texttt{Variable} to \texttt{Variable} or \texttt{Term}.
  \item \texttt{ListVar} to \texttt{VarList} or \texttt{VarSet}
    or \texttt{[Term]} and maybe \texttt{[ListVar]}.
\end{itemize}
However,
we have a number of constraints regarding compatibility
between pattern variables  and their corresponding candidate bindings,
based on variable class and temporality.

Basically observation variables can be bound to both observation
and expression variables, as can expression variables%
\footnote{This was originally not allowed, but is required when matching
list-variables as replacements in substitutions, e.g. $[O_m/O] :: [\lst e/\lst x]$.}
%
while predicate variables can only be bound to
variables of the same class
(Fig. \ref{fig:utp-perm-class-bind}).
\begin{figure}
  \begin{center}
    \begin{tabular}{|c|c|c|c|}
      \hline
       pattern: & \texttt{ObsV} & \texttt{ExprV} & \texttt{PredV}
    \\ $\downarrow$ &&&
    \\ \underline{candidate} &&&
    \\\hline
       \texttt{ObsV} & Yes & Yes &  No
    \\\hline
       \texttt{ExprV} & Yes & Yes & No
    \\\hline
       \texttt{PredV} & No & No & Yes
    \\\hline
    \end{tabular}
  \caption{Permissible variable class binding combinations. }
  \label{fig:utp-perm-class-bind}
  \end{center}
\end{figure}
\begin{code}
validVarClassBinding :: VarClass -> VarClass -> Bool
validVarClassBinding ObsV  ObsV   =  True
validVarClassBinding ObsV  ExprV  =  True
validVarClassBinding ExprV ObsV   =  True
validVarClassBinding ExprV ExprV  =  True
validVarClassBinding PredV PredV  =  True
validVarClassBinding _     _      =  False
\end{code}
A similar predicate for binding to terms:
\begin{code}
validVarTermBinding :: VarClass -> TermKind -> Bool
validVarTermBinding ObsV  (E _)  =  True
validVarTermBinding ExprV (E _)  =  True
validVarTermBinding PredV P      =  True
validVarTermBinding _     _      =  False
\end{code}

As far as temporality goes,
Static can bind to anything.
Textual can only bind to Textual \emph{variables},
and other dynamics can only bind to the same temporality
(Fig. \ref{fig:utp-perm-time-bind}).
\begin{figure}
  \begin{center}
    \begin{tabular}{|c|c|l|}
      \hline
      pattern && allowed candidates
    \\\hline
       \texttt{Textual}
       &$\mapsto$&
       \texttt{Textual}
    \\\hline
       \texttt{Static}
       &$\mapsto$&
       \texttt{Static}, \texttt{Textual},
       \texttt{Before}, \texttt{During}, \texttt{After}
    \\\hline
       $d$ &$\mapsto$&
       $d$, for $d$ in
       \texttt{Before}, \texttt{During}, \texttt{After}
    \\\hline
    \end{tabular}
  \caption{Permissible variable temporality binding combinations. }
  \label{fig:utp-perm-time-bind}
  \end{center}
\end{figure}
\begin{code}
validVarTimeBinding :: VarWhen -> VarWhen -> Bool
validVarTimeBinding Textual cwhen  =  cwhen == Textual
validVarTimeBinding Static  _      =  True
validVarTimeBinding pwhen   cwhen  =  cwhen == pwhen
\end{code}
In a scenario where $a$ binds to $b$,
if $a$ is dynamic,
then binding respects temporality
($a \mapsto b, a' \mapsto b', a_m \mapsto b_n, \texttt{a} \mapsto \texttt{b}$).
Also any one of those bindings induces all the others.

\begin{figure}
  \begin{center}
    \begin{tabular}{|l|c|c|c|c|c|c|c|c|l|}
    \hline
      looking up:
      & $u$ & $v$& $u'$ & $v'$& $u_a$ & $v_a$& $u_b$ & $v_b$
      & Need to record:
    \\\hline
      after inserting\dots &&&&&&&&&
    \\\hline
      first  $u' \mapsto x'$ (1),
      & $x$ & - & $x'$ & - & - & - & - & -
      & $u \mapsto x$
    \\\hline
      then $v_a \mapsto y_m$ (2),
      & $x$ & $y$ & $x'$ & $y'$ & $x_m$ & $y_m$ & - & - &
      $u \mapsto x, v \mapsto y, a \mapsto m $
    \\\hline
      then  $u_b \mapsto x_n$ (3).
      & $x$ & $y$ & $x'$ & $y'$ & $x_m$ & $y_m$ & $x_n$ & $y_m$ &
      $u \mapsto x, v \mapsto y, a \mapsto m, b \mapsto n $
    \\\hline
    \end{tabular}
  \caption{Inducing dynamic bindings---a scenario. }
  \label{fig:utp-dynamic-inducing}
  \end{center}
\end{figure}

The following scenario (see also Fig. \ref{fig:utp-dynamic-inducing})
illustrates how dynamic variable binding should work,
given an initial empty binding:
\begin{enumerate}
  \item First, inserting a binding from $u'$ to $x'$ means that we
    can now lookup both $u$ and $u'$ to get $x$ and $x'$ respectively.
    However we cannot lookup $u_s$ for any subscript because we don't know
    what the corresponding subscript should be for $x$.
  \item Next, adding a binding from $v_a$ to $y_m$ means we can now lookup
    $v$, $v'$ and $v_a$ to get $y$, $y'$ and $y_m$.
    But also, a lookup of $u_a$ will suceed, returning $x_m$,
    because we now know that subscript $a$ binds to subscript $m$.
  \item Finally, a binding from $u_b$ to $x_n$%
  \footnote{If $u_b$ tries to bind to any subscripted variable other than $x$
  then the attempt will fail.}
   results in one new piece of binding information
   that says that subscript $b$ binds to $n$.
\end{enumerate}


We expect the behaviour shown in Fig. \ref{fig:dynamic-coherence}.
\begin{figure}
\begin{center}
\begin{tabular}{|c|c|c|c|}
\hline
   new entry: & $s \mapsto x$
              & $v \mapsto x$, $v' \mapsto x'$, $\texttt{v} \mapsto \texttt{x}$
              & $v_m \mapsto x_n$
\\\hline
  inserted as: & $i_s \mapsto x$
             & $i_v \mapsto x_{\_}$
             & $i_v \mapsto x_n$
\\\hline
  \underline{prior bind} & \multicolumn{3}{|c|}{\underline{actual binding outcome}}
\\\hline
  none & $i_s\mapsto x$ & $i_v \mapsto x_{\_}$ & $i_v \mapsto x_n$
\\\hline
  $i_s \mapsto x$ & $i_s\mapsto x$ &  &
\\\hline
  $i_s \mapsto y, y\neq x$ & FAIL &  &
\\\hline
  $i_v \mapsto x_{\_}$ && $i_v \mapsto x_{\_}$ & $i_v \mapsto x_n$
\\\hline
  $i_v \mapsto x_n$ && $i_v \mapsto x_n$ & $i_v \mapsto x_n$
\\\hline
  $i_v \mapsto x_a, a\neq n$ && $i_v \mapsto x_a$ & FAIL
\\\hline
  $i_v \mapsto y_a, y\neq x$ && FAIL & FAIL
\\\hline
\end{tabular}
  \caption{
    Managing Dynamic binding coherence,
    where
    $s$ is \texttt{Static},
    $\texttt{v}$ and $\texttt{x}$ are \texttt{Textual},
    and $v$ and $x$ with or without decoration,
    are any other \texttt{Dynamic},
    and $i_s$ and $i_v$ are
    the respective identifiers underlying $s$ and the $v$s
  }
  \label{fig:dynamic-coherence}
\end{center}
\end{figure}



The key issue here is how each single binding inserted,
of a given temporality,
also induces bindings for the same variable identifiers,
but with as many other temporalities as is possible.
From all of this we can see that we need to record
identifier-identifier bindings along with subscript-subscript bindings,
for dynamic variables,
and identifier to variable bindings for static variables.
Given that similar rules apply to list variables,
we find that, in effect, we need to maintain at least three mappings:
\begin{description}
  \item[Variable to \dots]
    Mapping of variable identifier and class,
    to either variables or identifier and class or terms.
  \item[Subscript to \dots]
    Mapping of subscripts to subscripts.
  \item[List-Variable to \dots]
    Mapping of list-variable identifiers, class and identifier-lists,
    to lists and sets of general variables, as well as lists of terms.
\end{description}

For substitution matching we are dealing with a set of target/replacement pairs.
These come in two kinds,
the first being a ``traditional'' variable/term pair,
which as a pattern should match one such pair in the candidate.
The other form is that of a pair of two list-variables,
one as target, the other as replacement.
The target-list-variable needs to match a list of targets of either kind,
while the replacement list-variable needs to match a \textbf{corresponding} list
of replacement terms and list-variables.
In effect, a list-variable target/replacement pattern
needs to match a substitution!
However, all we need to do is allow a mapping from a list-variable
to a list of terms to also include a list of list-variables.


\newpage
\subsection{Binding Types}

\subsubsection{Binding \texttt{Variable} to \texttt{Variable} or \texttt{Term}}

We bind a variable identifier to either a identifier, variable or term:
\begin{code}
data VarBind = BI Identifier | BV Variable | BT Term deriving (Eq, Ord, Show, Read)

type VarBinding = M.Map (Identifier,VarClass) VarBind
\end{code}
We return just the variable or term from a lookup:
\begin{code}
pattern BindVar  v  =  BV v
pattern BindTerm t  =  BT t
\end{code}

\subsubsection{
  Binding \texttt{Subscript} to \texttt{Subscript}
}

We bind a subscript to a subscript.
\begin{code}
type SubBinding = M.Map Subscript Subscript
\end{code}

\subsubsection{
  Binding \texttt{ListVar} to
  \texttt{VarList}, or \texttt{VarSet},
  or a mixed \texttt{ListVar}/\texttt{Term} list.
}
\begin{code}
type LVarOrTerm = Either ListVar Term

injLV :: ListVar    -> LVarOrTerm ; injLV lv = Left  lv
injTM :: Term       -> LVarOrTerm ; injTM tm = Right tm
lvOf  :: LVarOrTerm -> ListVar    ; lvOf = fromLeft  (error "lvOf: not ListVar")
tmOf  :: LVarOrTerm -> Term       ; tmOf = fromRight (error "tmOf: not Term")

lvsOf     :: [LVarOrTerm] -> [ListVar]          ; lvsOf = lefts
tmsOf     :: [LVarOrTerm] -> [Term]             ; tmsOf = rights
lvtmSplit :: [LVarOrTerm] -> ([ListVar],[Term]) ; lvtmSplit = partitionEithers
\end{code}

We bind a list-variable to either a list or set of variables,
or a list that mixes terms and list-variables.
This latter is used when matching substitutions and iterations.
We use the variable identifier, class, and the list of `subtracted` identifiers
as the map key.
\begin{code}
data LstVarBind
 = BL  VarList
 | BS  VarSet
 | BX  [LVarOrTerm]
 deriving (Eq, Ord, Show, Read)

type ListVarKey = (Identifier,VarClass,[Identifier],[Identifier])

type ListVarBinding
              = M.Map ListVarKey LstVarBind
\end{code}

We return the variable list or set, or term+lvar-list from a lookup:
\begin{code}
pattern BindList vl      =  BL vl
pattern BindSet  vs      =  BS vs
pattern BindTLVs tlvs    =  BX tlvs
\end{code}

We put these together:
\begin{code}
newtype Binding = BD (VarBinding, SubBinding, ListVarBinding)
 deriving (Eq, Ord, Show, Read)

emptyBinding :: Binding
emptyBinding = BD (M.empty, M.empty, M.empty)
\end{code}

Merging a binding (first takes precedence!):
\begin{code}
mergeBindings (BD (vb1,sb1,lvb1)) (BD (vb2,sb2,lvb2))
  = BD(vb1 `M.union` vb2, sb1 `M.union` sb2, lvb1 `M.union` lvb2)
\end{code}

\newpage
\subsection{Binding Insertion}

If a variable is already present,
then the new binding must be `equivalent',
otherwise we fail.
Even though equivalent, we might still update the binding.
This is to allow specialisation of a pre-existing binding
where this is useful.

We define a generic insertion function as follows.
To give good feedback on a failed binding,
we need a descriptive string, the domain value,
the existing binding, along with the two conflicting range values,
resulting in the following monadic checker type:
\begin{code}
type UpdateCheck m d r  =  d  -- domain element
                        -> Map d r  -- mapping
                        -> r        -- new range element
                        -> r        -- old range element
                        -> m r      -- resulting range element
\end{code}

Insertion first looks to see if the domain element is already
present. If not, the mapping is made.
If present, then the update function checks if old and new
are equivalent, and proposes what the new range element should be.
\begin{code}
insertDR :: (Show d, Show r, Ord d, Monad m, MonadFail m)
         => UpdateCheck m d r
         -> d -> r -> Map d r
         -> m (Map d r)
insertDR rEqv d r binding
 = case M.lookup d binding of
     Nothing  ->  return $ M.insert d r binding
     Just r0  ->  do r' <- rEqv d binding r r0
                     return $ M.insert d r' binding
\end{code}

The most common case is when equivalence needs to be equality:
\begin{code}
rangeEq :: (Show d, Show r, Ord d, Eq r, Monad m, MonadFail m)
        => String -> UpdateCheck m d r
rangeEq nAPI d binding r r0
 | r == r0    =  return r
 | otherwise  =  fail $ unlines
                  [ (nAPI++": already bound differently.")
                  , "d = " ++ show d
                  , "old r = " ++ show r0
                  , "new r = " ++ show r
                  , "bind:\n" ++ show binding
                  ]
\end{code}

\newpage
\subsubsection{Binding Subscript to Subscript}

\begin{code}
bindSubscriptToSubscript :: (Monad m, MonadFail m)
                         => String -> VarWhen -> VarWhen -> SubBinding
                         -> m SubBinding
bindSubscriptToSubscript what (During m) (During n) sbind
  = insertDR (rangeEq what) m n sbind
bindSubscriptToSubscript what vw1 vw2 sbind
 | vw1 == vw2      =  return sbind
 | vw1 == Static   =  return sbind
 | otherwise  =  fail $ unlines'
                  [ what
                  , "incompatible temporality"
                  , "vw1 = "++show vw1
                  , "vw2 = "++show vw2
                  ]
\end{code}

\newpage
\subsubsection{Binding Variable to Variable}

\begin{code}
bindVarToVar :: (Monad m, MonadFail m) => Variable -> Variable -> Binding -> m Binding
\end{code}


A \texttt{Static} variable can bind to
any non-\texttt{Textual} thing in the appropriate class.
\begin{code}
bindVarToVar (Vbl vi vc Static) x@(Vbl xi xc xw)
             (BD (vbind,sbind,lbind))
 | validVarClassBinding vc xc
   =  do vbind' <- insertDR (rangeEq "bindVarToVar(Static)")
                            (vi,vc) (BV x) vbind
         return $ BD (vbind',sbind,lbind)
 | otherwise      =  fail "bindVarToVar: incompatible Static classes"
\end{code}

A \texttt{During} variable can only bind to a \texttt{During} variable
in the appropriate class.
\begin{code}
bindVarToVar (Vbl vi vc (During m)) x@(Vbl xi xc (During n))
             (BD (vbind,sbind,lbind))
 | validVarClassBinding vc xc
   =  do vbind' <- insertDR (rangeEq "bindVarToVar(During)")
                            (vi,vc) (BI xi) vbind
         sbind' <- insertDR (rangeEq "bindVarToVar(Subscript)") m n sbind
         return $ BD (vbind',sbind',lbind)
 | otherwise  =  fail "bindVarToVar: incompatible During classes"
\end{code}

A dynamic variable can only bind to a dynamic variable of the same
temporality in the appropriate class.
\begin{code}
bindVarToVar dv@(Vbl vi vc vw) rv@(Vbl xi xc xw)
             (BD (vbind,sbind,lbind))
 | vw /= xw   =  fail "bindVarToVar: different temporalities"
 | validVarClassBinding vc xc
   =  do vbind' <- insertDR (rangeEq "bindVarToVar(dynamic)")
                            (vi,vc) (BI xi) vbind
         return $ BD (vbind',sbind,lbind)
 | otherwise
    =  fail $ unlines
          [ "bindVarToVar: incompatible variables"
          , "dv = " ++ show dv
          , "rv = " ++ show rv
          ]
\end{code}

Can be useful to bind a list of (pattern/candidate) variables pairs:
\begin{code}
bindVarsToVars :: (Monad m, MonadFail m) => [(Variable, Variable)] -> Binding -> m Binding
bindVarsToVars [] bind = return bind
bindVarsToVars ((dv,rv):rest) bind
  = do bind' <- bindVarToVar dv rv bind
       bindVarsToVars rest bind'
\end{code}

Also useful is binding a (list of) pattern variable(s)
to itself (themselves):
\begin{code}
bindVarToSelf :: (Monad m, MonadFail m) => Variable -> Binding -> m Binding
bindVarToSelf v bind = bindVarToVar v v bind

bindVarsToSelves :: (Monad m, MonadFail m) => [Variable] -> Binding -> m Binding
bindVarsToSelves [] bind = return bind
bindVarsToSelves (v:vs) bind
  = do bind' <- bindVarToSelf v bind
       bindVarsToSelves vs bind'
\end{code}


\newpage
\subsubsection{Binding Variable to Term}

An observation or expression variable can bind to an expression
while a predicate variable can only bind to a predicate.
\begin{code}
bindVarToTerm :: (Monad m, MonadFail m) => Variable -> Term -> Binding -> m Binding
\end{code}

If we are binding to a term with variant \texttt{Var},
we pass over to \texttt{bindVarToVar}.
\begin{code}
bindVarToTerm pv ct@(Var _ cv) binds = bindVarToVar pv cv binds
\end{code}

A \texttt{Textual} pattern variable cannot bind to a term
\begin{code}
bindVarToTerm pv@(Vbl _ _ Textual) _ binds
 = fail "bindVarToTerm: textual patterns not allowed.,"
\end{code}

Static patterns bind to anything in the appropriate class,
as per Fig.\ref{fig:utp-perm-class-bind}.
\begin{code}
bindVarToTerm v@(Vbl vi vc Static) ct (BD (vbind,sbind,lbind))
 | validVarTermBinding vc (termkind ct)
   = do vbind' <- insertDR (rangeEq "bindVarToTerm") (vi,vc) (BT ct) vbind
        return $ BD (vbind',sbind,lbind)
 | otherwise = fail "bindVarToTerm: incompatible variable and term."
\end{code}

All remaining pattern cases are non-\texttt{Textual} dynamic variables.

Dynamic observables cannot bind to terms.
\begin{code}
bindVarToTerm pv@(Vbl v ObsV _) ct binds
 = fail "bindVarToTerm: dynamic observable cannot bind to term."
\end{code}

Dynamic expression variables can only bind to
expression terms, all of whose dynamic variables have the same temporality.
Regardless of the temporality of the pattern variable,
we always store the term with temporality \texttt{Before}.
This avoids having to compare terms modulo temporality
during insertion.
\begin{code}
bindVarToTerm v@(Vbl vi ExprV vt) ct (BD (vbind,sbind,lbind))
 | isPred ct   =  fail "bindVarToTerm: e.-var. cannot bind predicate."
 | wsize  > 1  =  fail "bindVarToTerm: e.-var. mixed term temporality."
 | wsize == 0  -- term has no variables
   = do vbind' <- insertDR (rangeEq "bindVarToTerm(ev1)") (vi,ExprV) (BT ct) vbind
        return $ BD (vbind',sbind,lbind)
 | otherwise -- term has one temporality
    = do sbind' <- bindSubscriptToSubscript "bindVarToTerm(ev2)" vt thectw sbind
         vbind' <- insertDR (rangeEq "bindVarToTerm(ev3)") (vi,ExprV) (dnTerm2VarBind ct) vbind
         return $ BD (vbind',sbind',lbind)
 where
   ctws = temporalityOf ct
   wsize = S.size ctws
   thectw = S.elemAt 0 ctws
\end{code}

\newpage
Dynamic predicate variables can only bind to
predicate terms, all of whose dynamic variables have the same temporality.
\begin{code}
bindVarToTerm v@(Vbl vi PredV vt) ct (BD (vbind,sbind,lbind))
 | isExpr ct  =  fail "bindVarToTerm: p.-var. cannot bind expression."
 | wsize  > 1  =  fail "bindVarToTerm: p.-var. mixed term temporality."
 | wsize == 0  -- term has no variables
   = do vbind' <- insertDR (rangeEq "bindVarToTerm(pv1)") (vi,PredV) (dnTerm2VarBind ct) vbind
        return $ BD (vbind',sbind,lbind)
 | otherwise
    = do sbind' <- bindSubscriptToSubscript "bindVarToTerm(pv2)" vt thectw sbind
         vbind' <- insertDR (rangeEq "bindVarToTerm(pv3)") (vi,PredV) (dnTerm2VarBind ct) vbind
         return $ BD (vbind',sbind',lbind)
 where
   ctws = temporalityOf ct
   wsize = S.size ctws
   thectw = S.elemAt 0 ctws
\end{code}

Catch-all
\begin{code}
bindVarToTerm pv ct _
 = fail $ unlines
     [ "bindVarToTerm: fell off end"
     , "pv = " ++ show pv
     , "ct = " ++ show ct ]
\end{code}

\newpage
Determining the temporality of a term:
\begin{code}
temporalityOf :: Term -> Set VarWhen
temporalityOf t = termTmpr S.empty [] t

-- for now we process all variables in the same way,
-- regardless of whether their occurrence is free, binding or bound.
-- this may make the binding too conservative
termTmpr vws ts (Var _ (Vbl _ _ vw))   =  termsTmpr (S.insert vw vws) ts
termTmpr vws ts (Cons _ _ _ ts')       =  termsTmpr vws (ts'++ts)
termTmpr vws ts (Bnd _ _ vs t)         =  vlTmpr    vws (t:ts) $ S.toList vs
termTmpr vws ts (Lam _ _ vl t)         =  vlTmpr    vws (t:ts) vl
termTmpr vsw ts (Cls _ t)              =  vsw -- not termsTmpr vsw ts t
termTmpr vws ts (Sub _ t sub)          =  subTmpr   vws (t:ts) sub
termTmpr vws ts (Iter tk _ _ _ _ lvs)  =  vlTmpr    vws ts $ map LstVar lvs
termTmpr vws ts _                      =  termsTmpr vws ts

temporalitiesOf :: [Term] -> Set VarWhen
temporalitiesOf ts = termsTmpr S.empty ts

termsTmpr vws []      =  vws
termsTmpr vws (t:ts)  =  termTmpr vws ts t

vlTmpr vws ts []                                = termsTmpr vws ts
vlTmpr vws ts (StdVar (Vbl _ _ vw):lv)          = vlTmpr (S.insert vw vws) ts lv
vlTmpr vws ts (LstVar (LVbl (Vbl _ _ vw) _ _):lv)
                                                = vlTmpr (S.insert vw vws) ts lv

subTmpr vws ts (Substn tsub lvsub)  =  subTmpr' vws ts tsub lvsub
subTmpr' vws ts tsub lvsub          =  lvsubTmpr vws ts tsub $ S.toList lvsub

substTemporalityOf tsub lvsub = subTmpr' S.empty [] tsub lvsub

lvsubTmpr vws ts tsub []  =  tsubTmpr vws ts $ S.toList tsub
lvsubTmpr vws ts tsub ((LVbl (Vbl _ _ vw1) _ _,LVbl (Vbl _ _ vw2) _ _):lvsub)
 = lvsubTmpr (S.fromList [vw1,vw2] `S.union` vws) ts tsub lvsub

subTgtTmpr tsub lvsub
 = S.map (timeVar . fst) tsub
   `S.union`
   S.map (timeLVar . fst) lvsub

subReplTmpr tsub lvsub
 = temporalitiesOf (map snd $ S.toList tsub)
   `S.union`
   S.map (timeLVar . snd) lvsub

tsubTmpr vws ts tsub = let (vs,ts') = unzip tsub in vsTmpr vws (ts'++ts) vs

vsTmpr vws ts []                 =  termsTmpr vws ts
vsTmpr vws ts ((Vbl _ _ vw):vs)  =  vsTmpr (S.insert vw vws) ts vs
\end{code}

\newpage
Dynamic normalisation (d.n.):
When we store a dynamic term,
we ``normalise'' it by setting its temporality to \texttt{Before}.

\begin{code}
dnTerm2VarBind :: Term -> VarBind
dnTerm2VarBind t = BT $ dnTerm t
\end{code}


\newpage
\subsubsection{Binding List-Variables to Variable-Lists}

The reason for having special ``list-variables''
is so we can refer to variable lists (and sets).
Here we implement the corresponding binding.
\begin{code}
bindLVarToVList :: (Monad m, MonadFail m) => ListVar -> VarList -> Binding
                           -> m Binding
\end{code}
We have two orthogonal well-formedness criteria for any such binding
($\lst\ell\less V  \mapsto \seqof{g_1,\dots,g_n}$):
\begin{itemize}
  \item
    The class and temporality of $\lst\ell$
    must agree with that of all the $g_i$.
  \item
    If one or more of the $g_i$ are themselves of the form $\lst\ell\less W$,
    then we need to check that that subset,
    viewed collectively,
    is no larger than $\lst\ell\less V$,
    and,
    if smaller,
    there are other $g_j$ that can make up the deficit
    (at least in principle).
    We refer to this as the feasibility of self-references in such a binding.
\end{itemize}

A \texttt{Static} list-variable binds to any variable-list
without \texttt{Textual} variables.
\begin{code}
bindLVarToVList lv@(LVbl (Vbl i vc Static) is ij) vl (BD (vbind,sbind,lbind))
 | all (validStaticGVarClass vc) vl
    =  do feasibility <- feasibleSelfReference lv vl
          lbind' <- insertDR (rangeEqvLSSub "bindLVarToVList(static)")
                             (i,vc,is,ij) (BL vl) lbind
          case feasibility of
            Nothing -> return $ BD (vbind,sbind,lbind')
            Just (vs,lv')
             -> do bind' <- attemptFeasibleBinding lv lv'
                                                   (BD (vbind,sbind,lbind'))
                   return bind'
 | otherwise = fail "bindLVarToVList: Static incompatibility"
\end{code}


A dynamic list-variable binds to any list of dynamic variables
all of which have the same class and temporality as itself.
\begin{code}
bindLVarToVList lv@(LVbl (Vbl i vc vw) is ij) vl (BD (vbind,sbind,lbind))
 | valid
    = do feasibility <- feasibleSelfReference lv vl
         sbind' <- bindSubscriptToSubscript "bindLVarToVList(1)" vw vlw sbind
         lbind' <- insertDR (rangeEqvLSSub "bindLVarToVList(2)")
                            (i,vc,is,ij) (BL $ map dnGVar vl) lbind
         case feasibility of
           Nothing -> return $ BD (vbind,sbind',lbind')
           Just (vs,lv')
            -> do bind' <- attemptFeasibleBinding lv lv'
                                                  (BD (vbind,sbind',lbind'))
                  return bind'
 | otherwise = fail "bindLVarToVList: dynamic incompatibility"
 where
   (valid, vlw) = vlCompatible vc vw vl
\end{code}

Anything else fails.
\begin{code}
bindLVarToVList _ _ _ = fail "bindLVarToVList: invalid lvar. -> vlist binding."
\end{code}

If the list-variable is static,
then we need to ensure that all the variable-list
variables
have a class compatible with that of the list variable.
\begin{code}
validStaticGVarClass :: VarClass -> GenVar -> Bool
validStaticGVarClass vc gvar  =  validVarClassBinding vc (gvarClass gvar)
\end{code}

\newpage
For a dynamic list-variable binding we require all variables in the list
to have a class compatible with the list variable,
and to have the same temporality.
\begin{code}
vlCompatible :: VarClass -> VarWhen -> VarList -> (Bool, VarWhen)
vlCompatible vc vw vl  =  vlComp vc vw S.empty vl

vlComp _ vw vws []
 | S.null vws  =  (True, vw)
 | otherwise   =  (True, S.elemAt 0 vws)
vlComp vc vw vws (gv:gvs)
 | gvw == Static                           =  (False, undefined)
 | validVarClassBinding vc (gvarClass gv)
   && S.size vws' <= 1                     =  vlComp vc vw vws' gvs
 | otherwise                               =  (False, undefined)
 where
   gvw = gvarWhen gv
   vws' = S.insert gvw vws
\end{code}

\subsubsection{Feasible Self-Reference}

If the list-variable is known, and occurs in the variable list,
then we need to check that the binding is feasible.
Consider the following (proposed) binding:
$$
  \lst\ell\less V
  \mapsto
  \seqof{ v_1,\dots,v_a
        , \lst v_1,\dots,\lst v_b
        , \lst\ell\less{W_1},\dots,\lst\ell\less{W_c}}
$$
The first thing that we note is that $V$ is a set of variables
in the pattern term,
whilst the variables $v_i$, $\lst v_j$, and variable-sets $W_k$
involve variables from the candidate.
So we will analyse the binding rhs first, to simplify it and check it,
and then may be able to deduce possible new bindings from elements of $V$
to parts of the (simplified) rhs.

As an example, consider the pattern
$
 x' = e \land \lst O'\less x = \lst O\less x
$
\\ with candidate
$
 a' = g \land b' = b \land \lst O'\less{a,b} = \lst O\less {a,b}
$
\\The resulting binding is
$
 \{ x \mapsto a
  , e \mapsto g
  , \lst O\less x \mapsto \seqof{b,\lst O\less{a,b}}
 \}
$
\\We don't need to assume that the $x$ binding is done first.
We can simplify $\seqof{b,\lst O\less{a,b}}$ to $\seqof{\lst O\less a}$.
We can then deduce from this the need for a $x \mapsto a$ binding.

The key idea is to fuse together components of the binding rhs
to their simplest form, and then compare its size
with that of the binding lhs.
The key rules are:
\begin{itemize}
  \item
    Combining $\lst O\less{W_1}$ with $\lst O\less{W_2}$
    results in $\lst O\less{W_1 \cap W_2}$.
  \item
    Combining variable set $X$ with list-variable $\lst O\less W$ results in
    variable set $X$ combined with $\lst O \less{(W\setminus X)}$.
\end{itemize}
We get an outcome of the form $X_S \cup X_L \cup \lst O\less{W_S,W_L}$,
where $X_S$ and $W_S$ are disjoint standard variable sets,
and $X_L$ and $W_L$ are disjoint list-variable sets.
So we now have a new binding, where the rhs is now a variable-set:
$$
  \lst O\less V
  \mapsto
  X_S \cup X_L \cup \lst O\less{W_S,W_L}
$$
This is feasible if
matching $V$ against $(W_S \cup W_L)$
is compatible with other bindings.
\begin{code}
feasibleSelfReference :: (Monad m, MonadFail m) => ListVar -> VarList
                                 -> m (Maybe(VarList,ListVar))
feasibleSelfReference lv vl
  | null selfrefs  =  return Nothing
  | feasibleListSizing lv otherVars finalSR
     = return $ Just (otherVars,finalSR)
  | otherwise      =  fail $ unlines'
                         [ "bindLVarToVs: infeasible self-reference"
                         , "lv = " ++ show lv
                         , "vl = " ++ show vl
                         , "otherVars = " ++ show otherVars
                         , "finalSR =" ++ show finalSR
                         ]
  where
    (selfrefs,otherVars) = partition (selfref $ varOf lv) vl
    (sr1:srrest) = map theLstVar selfrefs
    combinedSR = selfRefCombine sr1 srrest
    finalSR = otherCombine otherVars combinedSR
\end{code}
\newpage
Combining code:
\begin{code}
selfref :: Variable -> GenVar -> Bool
selfref v (LstVar lv)  =  varOf lv == v
selfref _ _            =  False

selfRefCombine :: ListVar -> [ListVar] -> ListVar
selfRefCombine sr [] = sr
selfRefCombine sr (sr':srrest)  =  selfRefCombine (sr `srmrg` sr') srrest

srmrg :: ListVar -> ListVar -> ListVar
(LVbl v is1 js1) `srmrg` (LVbl _ is2 js2)
  =  LVbl v (is1 `intersect` is2) (js1 `intersect` js2)

otherCombine :: VarList -> ListVar -> ListVar
otherCombine [] lv  =  lv
otherCombine vl@(gv:_) (LVbl v is js)
  = LVbl v (is \\ vlis) (js \\ vljs)
  where
    ( vlis, vljs ) = idsOf vl
\end{code}


Now we do the test for feasible sizing.
We have a binding which is semantically the same as:
$$
\lst O\less {V_S,V_L}
\mapsto
X_S \cup X_L \cup \lst O\less{W_S,W_L}
$$
where $X_S$ and $W_S$ are disjoint standard variable sets,
and $X_L$ and $W_L$ are disjoint list-variable sets.
\begin{itemize}
  \item
    The cardinality of $\lst O\less {V_S,V_L}$
    is less than or equal to that of $V_S$
    (equal if $V_L=\emptyset$).
    \item
      The cardinality of $\lst O\less {W_S,W_L}$
      is less than or equal to that of $W_S$
      (equal if $W_L=\emptyset$).
    \item
      The cardinality of $X_S \cup X_L$
      is greater than or equal to that of $X_S$
      (equal if $X_L=\emptyset$).
\end{itemize}
To be feasible, it must be possible for the lhs and rhs of the binding to have the same cardinality.
If we interpet each set as its cardinality,
we get the following formula:
$$
\lst O - (V_S + V_L)
=
X_S + X_L + \lst O - (W_S + W_L)
$$
Here $V_S$, $X_S$, and $W_S$ are \emph{known} fixed numbers,
while $V_L$, $X_L$, and $W_L$ can take any value from zero upwards if non-empty,
but equal precisely zero if empty.
We first eliminate $\lst O$ from each side,
realising that this means we do not need to know its cardinality.
$$
- V_S - V_L
=
X_S + X_L - W_S - W_L
$$
We move all the fixed numbers to the righthand side,
and the variable ones to the left:
$$
W_L - V_L - X_L
=
X_S + V_S - W_S
$$
We refer to $X_S + V_S - W_S$ as the ``kernel''.

We consider three possibilities for the kernel:

\begin{tabular}{|c|p{4.5in}|}
  \hline
   Kernel Value & Required LHS
\\\hline
   $ X_S + V_S - W_S = 0$
   & Match is feasible (all list vars, if any, map to empty) or $W_L = V_L+X_L$.
\\\hline
   $ X_S + V_S - W_S < 0$
   & At least one of $V_L$ or $X_L$ is non-zero to pull LHS down.
\\\hline
   $ X_S + V_S - W_S > 0$
   & $W_L$ must be non-zero to pull LHS up.
\\\hline
\end{tabular}

\newpage

\begin{code}
feasibleListSizing :: ListVar -> VarList -> ListVar -> Bool
feasibleListSizing (LVbl _ v_S v_L) rvars (LVbl _ w_S w_L)
  | kernel < 0  =  xL > 0 || vL > 0
  | kernel > 0  =  wL > 0
  | otherwise   =  True
  where
    (x_S,x_L) = partition isStdV rvars
    vS = length v_S
    xS = length x_S
    wS = length w_S
    kernel = xS + vS - wS
    vL = length v_L
    xL = length x_L
    wL = length w_L
\end{code}

We have a binding
$
  \lst O\less V
  \mapsto
  X\cup \lst O\less W
$
where $X$ and $W$ are disjoint that looks feasible.
If so, then we can deduce another matching between $V$ and $W$.
Rather than reproduce var-set to var-set matching here,
we look at simple cases:
\begin{itemize}
  \item
    $V = \setof{v}$,
    and $W = \setof w$,
    which requires $v \mapsto w$.
  \item
    $V = \setof{\lst\ell}$,
    which requires $\lst\ell \mapsto W$.
  \item
    $V = \setof{\lst\ell,\lst m}$,
    and $W = \setof{w,x}$,
    and $\lst\ell \mapsto \seqof{x}$,
    which requires $\lst m \mapsto \seqof{w}$.
    \\Generalising above:\\
    $V = \setof{\lst\ell,\lst m}$,
    and $X \subseteq W$,
    and $\lst\ell \mapsto X$,
    which requires $\lst m \mapsto W\setminus X$.
\end{itemize}

Here is a newer case:  $\lst\ell\less{x,y}$ to $\lst\ell\less{x,y,\lst x}$.

\begin{code}
attemptFeasibleBinding :: (Monad m, MonadFail m)
                       => ListVar  -- original list-variable being bound
                       -> ListVar  -- simplified self-reference
                       -> Binding -> m Binding
-- trivial case
attemptFeasibleBinding (LVbl _ [] []) (LVbl _ [] []) bind  =  return bind
\end{code}

$V = \setof{v}$,
and $W = \setof w$,
which requires $v \mapsto w$.
\begin{code}
attemptFeasibleBinding lV@(LVbl (Vbl _ vc vw) [vi] [])
                       lW@(LVbl _ [wi] [])
                       (BD (vbind,sbind,lbind))
  = do vbind' <- insertDR (rangeEq "bindVarToVar(feasible)")
                          (vi,vc) (BV $ Vbl wi vc $ dnWhen vw) vbind
       return $ BD  (vbind',sbind,lbind)
\end{code}

$V = \setof{\lst\ell}$,
which requires $\lst\ell \mapsto W$.
\begin{code}
attemptFeasibleBinding lV@(LVbl (Vbl _ vc vw) [] [vj])
                       lW@(LVbl _ wis wjs)
                       (BD (vbind,sbind,lbind))
  = do lbind' <- insertDR (rangeEqvLSSub "bindLVarToVList(feasible1)")
                          (vj,vc,[],[])
                          (BS $ S.fromList $(map StdVar wvs ++ map LstVar wlvs))
                          lbind
       return $ BD  (vbind,sbind,lbind')
  where
    vw' = dnWhen vw
    (wvs,wlvs) = makeVars vc vw' wis wjs
\end{code}

\newpage

$V = \setof{\lst\ell,\lst m}$,
and $X \subseteq W$,
and $\lst\ell \mapsto X$,
which requires $\lst m \mapsto W\setminus X$.
\begin{code}
attemptFeasibleBinding lV@(LVbl (Vbl _ vc vw) [] js@[li,mi])
                       lW@(LVbl _ wis wjs)
                       bind@(BD (vbind,sbind,lbind))
  | l_lvb /= Nothing
    = do x <- getVarSet l_lvb
         lbind' <- insertDR (rangeEqvLSSub "bindLVarToVList(feasible2)")
                          (mi,vc,[],[])
                          (BS (w S.\\ x))
                          lbind
         return $ BD  (vbind,sbind,lbind')
  | m_lvb /= Nothing
    = do x <- getVarSet m_lvb
         lbind' <- insertDR (rangeEqvLSSub "bindLVarToVList(feasible3)")
                          (li,vc,[],[])
                          (BS (w S.\\ x))
                          lbind
         return $ BD  (vbind,sbind,lbind')
  where
    vw' = dnWhen vw
    (wvs,wlvs) = makeVars vc vw' wis wjs
    w = S.fromList (map StdVar wvs ++ map LstVar wlvs)
    (_,[lvl,lvm]) = makeVars vc vw' [] js
    l_lvb = lookupLstBind bind lvl
    m_lvb = lookupLstBind bind lvm
    getVarSet Nothing           =  fail "attemptFeasibleBinding logic error"
    getVarSet (Just (BL vl))    =  return $ S.fromList vl
    getVarSet (Just (BS vs))    =  return vs
    getVarSet (Just (BX lvts))
     | null ts    =  return $ S.fromList $ map LstVar lvs
     | otherwise  =  do tvs <- sequence $ map termAsVar ts
                        return $ S.fromList
                               $ (map StdVar tvs ++ map LstVar lvs)
     where (lvs,ts) = lvtmSplit lvts
\end{code}


Everything else is too complicated right now!
\begin{code}
attemptFeasibleBinding lV lW bind
 = fail $ unlines'
    [ "feasibleBinding too complex!"
    , "lV   =  " ++ show lV
    , "lW   =  " ++ show lW
    , "bind =\n  " ++ show bind
    ]
\end{code}



\newpage
\subsubsection{Binding List-Variables to Variable-Sets}

When we are inserting a variable-set (\texttt{BS}),
we may find that a variable-list (\texttt{BL}) is present
(or vice versa).
Similarly,
when inserting a substitution replacement (\texttt{BX})
we may also find a variable-list
(or vice versa).
If they have ``equivalent'' elements,
then we update the set to be the list,
or the list to be substitution replacement, in the binding.
We require an equivalence for this:
\begin{code}
rangeEqvLSSub :: (Monad m, MonadFail m) => String -> UpdateCheck m ListVarKey LstVarBind
\end{code}
Variable Sets and Lists:
\begin{code}
rangeEqvLSSub nAPI lv binding list@(BL vl) (BS vs)
 | S.fromList vl == vs  =  return list
rangeEqvLSSub nAPI lv binding (BS vs) list@(BL vl)
 | S.fromList vl == vs  =  return list
\end{code}
Substitution Replacements and Variable Lists:
\begin{code}
rangeEqvLSSub nAPI lv binding (BL vl) srepl@(BX tlvs)
 | substReplEqv tlvs vl  =  return srepl
rangeEqvLSSub nAPI lv binding srepl@(BX tlvs) (BL vl)
 | substReplEqv tlvs vl  =  return srepl
\end{code}
Substitution Replacements and Variable Sets:
\begin{code}
rangeEqvLSSub nAPI lv binding (BS vs) srepl@(BX tlvs)
 | substReplEqv tlvs (S.toList vs)  =  return srepl
rangeEqvLSSub nAPI lv binding srepl@(BX tlvs) (BS vs)
 | substReplEqv tlvs (S.toList vs)  =  return srepl
\end{code}
If none of the above, then we expect full equality.
\begin{code}
rangeEqvLSSub nAPI lv binding vc1 vc2
 | vc1 == vc2  =  return vc1
 | otherwise  =  fail $ unlines
                  [ (nAPI++": already bound differently.")
                  , "lv = " ++ show lv
                  , "vc1 = " ++ show vc1
                  , "vc2 = " ++ show vc2
                  , "bind:\n" ++ show binding
                  ]
\end{code}

A variable list \texttt{vl}
is equivalent to a substitution replacement list
with a mix of terms \texttt{ts}
and list-variables \texttt{lvs}
if the two lists have the same length
and standard (list) variables in \texttt{vl}
correspond to terms (list variables) in \texttt{tlvs}.
\begin{code}
substReplEqv :: [Either ListVar Term] -> VarList -> Bool
substReplEqv [] []  =  True
substReplEqv (Right t:tlvs)   (StdVar v   : vl)
  | termVarEqv t v  =  substReplEqv tlvs vl
substReplEqv (Left lv:tlvs) (LstVar lv' : vl)
  | lv == lv'       =  substReplEqv tlvs vl
substReplEqv _  _   =  False

termVarEqv (Var _ u) v  =  u == v
termVarEqv _         _  =  False
\end{code}




\newpage
\subsubsection{Binding List-Variables to Variable-Sets}

Similar code to \texttt{bindLVarToVList} above, except we have sets.
\begin{code}
vsCompatible vc Static vs  =  (all (validStaticGVarClass vc) vs, Static)
vsCompatible vc vw vs      =  vlComp vc vw S.empty (S.toList vs)
\end{code}

\begin{code}
bindLVarToVSet :: (Monad m, MonadFail m) => ListVar -> VarSet -> Binding -> m Binding

bindLVarToVSet lv@(LVbl (Vbl i vc Static) is ij) vs (BD (vbind,sbind,lbind))
 | valid
    =  do feasibility <- feasibleSelfReference lv (S.toList vs)
          lbind' <- insertDR (rangeEqvLSSub "bindLVarToVSet(static)")
                             (i,vc,is,ij) (BS vs) lbind
          case feasibility of
            Nothing -> return $ BD (vbind,sbind,lbind')
            Just (vs',lv')
             -> do bind' <-  attemptFeasibleBinding lv lv'
                                                    (BD (vbind,sbind,lbind'))
                   return bind'
 | otherwise = fail $ unlines'
                [ "bindLVarToVSet: incompatible class in variable set."
                , "lv = "++show lv
                , "vs = "++show vs
                ]
 where
    (valid, vsw) = vsCompatible vc Static vs

bindLVarToVSet lv@(LVbl (Vbl i vc vw) is ij) vs (BD (vbind,sbind,lbind))
 | valid
    = do feasibility <- feasibleSelfReference lv (S.toList vs)
         sbind' <- bindSubscriptToSubscript "bindLVarToVSet(1)" vw vsw sbind
         lbind' <- insertDR (rangeEqvLSSub "bindLVarToVSet(2)")
                            (i,vc,is,ij) (bvs vs) lbind
         case feasibility of
           Nothing -> return $ BD (vbind,sbind',lbind')
           Just (vs',lv')
            -> do bind' <-  attemptFeasibleBinding lv lv'
                                                   (BD (vbind,sbind',lbind'))
                  return bind'
 | otherwise = fail "bindLVarToVSet: incompatible dynamic class."
 where
   (valid, vsw) = vsCompatible vc vw vs

bindLVarToVSet _ _ _ = fail "bindLVarToVSet: invalid lvar. -> vset binding."
\end{code}

\begin{code}
overrideLVarToVSet :: (Monad m, MonadFail m) => ListVar -> VarSet -> Binding -> m Binding
overrideLVarToVSet lv@(LVbl (Vbl i vc Static) is ij) vs (BD (vbind,sbind,lbind))
 | valid
    =  return $ BD (vbind,sbind, M.insert (i,vc,is,ij) (bvs vs) lbind)
 | otherwise = fail "overrideLVarToVSet: incompatible class in variable set."
 where
    (valid, vsw) = vsCompatible vc Static vs

overrideLVarToVSet lv@(LVbl (Vbl i vc vw) is ij) vs (BD (vbind,sbind,lbind))
 | valid
    = do sbind' <- bindSubscriptToSubscript "bindLVarToVSet(1)" vw vsw sbind
         return $ BD (vbind,sbind',M.insert (i,vc,is,ij) (bvs vs) lbind)
 | otherwise = fail "overrideLVarToVSet: incompatible dynamic class."
 where
   (valid, vsw) = vsCompatible vc vw vs

overrideLVarToVSet _ _ _ = fail "overrideLVarToVSet: invalid lvar. -> vset binding."
\end{code}

We need to coerce dynamics temporality to \texttt{Before}.
\begin{code}
bvs = BS . S.map dnGVar
\end{code}

\newpage
We also need some identity bindings:
\begin{code}
bindLVarToSSelf :: (Monad m, MonadFail m) => ListVar -> Binding -> m Binding
bindLVarToSSelf lv bind = bindLVarToVSet lv (S.singleton $ LstVar lv) bind

bindLVarsToSSelves :: (Monad m, MonadFail m) => [ListVar] -> Binding -> m Binding
bindLVarsToSSelves [] bind = return bind
bindLVarsToSSelves (lv:lvs) bind
  = do bind' <- bindLVarToSSelf lv bind
       bindLVarsToSSelves lvs bind'
\end{code}

And binding pairs:
\begin{code}
bindLVarSTuple :: (Monad m, MonadFail m) => (ListVar,ListVar) -> Binding -> m Binding
bindLVarSTuple (plv,clv) bind
                     = bindLVarToVSet plv (S.singleton $ LstVar clv) bind

bindLVarSTuples :: (Monad m, MonadFail m) => [(ListVar,ListVar)] -> Binding -> m Binding
bindLVarSTuples [] bind = return bind
bindLVarSTuples (lv2:lv2s) bind
  = do bind' <- bindLVarSTuple lv2 bind
       bindLVarSTuples lv2s bind'
\end{code}

\newpage
\subsubsection{Binding List-Variables to Substitution Replacements}

A list variable denoting a replacement(-list) in a substitution
may bind to a sequence of candidate replacement terms,
and list-variables.
As for \texttt{bindLVarToVList} above,
we will need to look out for list-variable self-references.
\begin{code}
bindLVarSubstRepl :: (Monad m, MonadFail m)
                  => ListVar -> [LVarOrTerm] -> Binding -> m Binding
\end{code}

A \texttt{Textual} pattern variable cannot bind to terms
\begin{code}
bindLVarSubstRepl (LVbl (Vbl _ _ Textual) _ _) _ binds
 = fail "bindLVarSubstRepl: textual list-vars. not allowed."
\end{code}

Static patterns bind to anything in the appropriate class,
as per Fig.\ref{fig:utp-perm-class-bind}.
\begin{code}
bindLVarSubstRepl lv@(LVbl (Vbl vi vc Static) is ij) cndTsVL (BD (vbind,sbind,lbind))
 | all (validVarTermBinding vc) (map termkind cndTs)
    = do feasibility <- feasibleSelfReference lv $ map LstVar cndVL
         lbind' <- insertDR (rangeEqvLSSub "bindLVarSubstRepl(static)")
                            (vi,vc,is,ij) (BX cndTsVL) lbind
         case feasibility of
           Nothing -> return $ BD (vbind,sbind,lbind')
           Just (vs,lv')
            -> do bind' <- attemptFeasibleBinding lv lv'
                                                  (BD (vbind,sbind,lbind'))
                  return bind'
 | otherwise  =  fail "bindLVarSubstRepl: incompatible variable and terms."
 where
   (cndVL,cndTs) = partitionEithers cndTsVL
\end{code}

All remaining pattern cases are non-\texttt{Textual} dynamic variables.

Dynamic predicate list-variables can only bind to
predicate terms, all of whose dynamic variables have the same temporality.
Dynamic observable and expression list-variables can only bind to
expression terms, all of whose dynamic variables have the same temporality.
\begin{code}
bindLVarSubstRepl lv@(LVbl (Vbl vi vc vt) is ij) cndTsVL (BD (vbind,sbind,lbind))
 | vc == PredV && any isExpr cndTs
           =  fail "bindLVarSubstRepl: pred. l-var. cannot bind to expression."
 | vc /= PredV && any isPred cndTs
           =  fail "bindLVarSubstRepl: non-pred. l-var. cannot bind to predicate."
 | wsize  > 1  =  fail "bindLVarSubstRepl: p.-var. mixed term temporality."
 | otherwise -- wsize == 0,1
    = do feasibility <- feasibleSelfReference lv $ map LstVar cndVL
         sbind' <- if wsize == 1
                     then bindSubscriptToSubscript "bindLVarSubstRepl(sbind)"
                                                   vt thectw sbind
                     else return sbind
         lbind' <- insertDR (rangeEqvLSSub "bindLVarSubstRepl(lbind)")
                            (vi,vc,is,ij) (BX (cndTsVL')) lbind
         case feasibility of
           Nothing ->  return $ BD (vbind,sbind',lbind')
           Just (vs,lv')
            -> do bind' <- attemptFeasibleBinding lv lv'
                                                  (BD (vbind,sbind',lbind'))
                  return bind'
 where
   (cndVL,cndTs) = partitionEithers cndTsVL
   ctws = temporalitiesOf cndTs
   wsize = S.size ctws
   thectw = S.elemAt 0 ctws
   dnLVarTerm (Right t) = Right $ dnTerm t
   dnLVarTerm (Left lv) = Left $ dnLVar lv
   cndTsVL' = map dnLVarTerm cndTsVL
\end{code}

Catch-all
\begin{code}
bindLVarSubstRepl plv cndTsVL _
 = fail $ unlines
     [ "bindLVarSubstRepl: fell off end"
     , "plv = " ++ show plv
     , "cndTsVL = " ++ show cndTsVL ]
\end{code}

A common use case:
\begin{code}
bindLVarToTList :: (Monad m, MonadFail m) => ListVar -> [Term] -> Binding -> m Binding
bindLVarToTList lv ts = bindLVarSubstRepl lv (map Right ts)
\end{code}


\newpage
\subsubsection{Binding General-Variables to General-Variables}

An list-variable can bind to a singleton list of any general variable,
while a standard-variable can only bind to a standard variable.
\begin{code}
bindGVarToGVar :: (Monad m, MonadFail m) => GenVar -> GenVar -> Binding -> m Binding
bindGVarToGVar (LstVar lv) gv binds = bindLVarToVList lv [gv] binds
bindGVarToGVar (StdVar pv) (StdVar cv) binds = bindVarToVar pv cv binds
bindGVarToGVar _ _ _ = fail "bindGVarToGVar: invalid stdvar. -> lstvar. binding."
\end{code}

\subsubsection{Binding General-Variables to Variable-Lists}

An list-variable can bind to a list of any length,
while a standard-variable can only bind to the standard variable inside
a singleton list.
\begin{code}
bindGVarToVList :: (Monad m, MonadFail m) => GenVar -> VarList -> Binding -> m Binding
bindGVarToVList (LstVar lv) vl binds = bindLVarToVList lv vl binds
bindGVarToVList (StdVar pv) [StdVar cv] binds = bindVarToVar pv cv binds
bindGVarToVList _ _ _ = fail "bindGVarToVList: invalid gvar. -> vlist binding."
\end{code}

\newpage
\subsection{Binding Lookup}

Binding lookup is very straightforward,
with the minor wrinkle that we need to ensure we lookup
the subscript binding if the lookup variable has \texttt{During} temporality.

\newpage
\subsubsection{Lookup (Standard) Variables}

\begin{code}
lookupVarBind :: (Monad m, MonadFail m) => Binding -> Variable -> m VarBind
lookupVarBind (BD (vbind,_,_)) v@(Vbl vi vc Static)
  = case M.lookup (vi,vc) vbind of
      Nothing  ->  fail ("lookupVarBind: Variable "++show v++" not found.")
      Just (BI xi) -> fail $ unlines
                       [ "lookupVarBind: Static bound to (BI xi)"
                       , "v = " ++ show v
                       , "xi = " ++ show xi
                       , "vbind:\n" ++ show vbind
                       ]
      Just vb  ->  return vb

lookupVarBind (BD (vbind,sbind,_)) v@(Vbl vi vc (During m))
  = case M.lookup m sbind of
     Nothing -> fail ("lookupVarBind: Subscript ''"++m++"'' not found.")
     Just n ->
       case M.lookup (vi,vc) vbind of
         Nothing  ->  fail ("lookupVarBind: Variable "++show v++" not found.")
         Just (BI xi)  ->  return $ BindVar  $ Vbl xi vc (During n)
         Just (BT xt)  ->  return $ BindTerm $ unTerm (During n) xt
         Just b -> fail $ unlines
                 [ "lookupVarBind: During was bound to BV"
                 , "v = " ++ show v
                 , "b = " ++ show b
                 , "vbind:\n" ++ show vbind
                 ]

lookupVarBind (BD (vbind,_,_)) v@(Vbl vi vc vw)
  = case M.lookup (vi,vc) vbind of
     Nothing  ->  fail ("lookupVarBind: Variable "++show v++" not found.")
     Just (BI xi)  ->  return $ BindVar  $ Vbl xi vc vw
     Just (BT xt)  ->  return $ BindTerm $ unTerm vw xt
     Just b -> fail $ unlines
             [ "lookupVarBind: Dynamic was bound to BV"
             , "v = " ++ show v
             , "b = " ++ show b
             , "vbind:\n" ++ show vbind
             ]
\end{code}

\newpage
\subsubsection{Lookup List-Variables}

List variable lookup is very similar:
\begin{code}
lookupLstBind :: (Monad m, MonadFail m) => Binding -> ListVar -> m LstVarBind

lookupLstBind (BD (_,_,lbind)) lv@(LVbl (Vbl i vc Static) is ij)
  = case M.lookup (i,vc,is,ij) lbind of
     Nothing   ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
     Just bvl  ->  return bvl

lookupLstBind (BD (_,sbind,lbind)) lv@(LVbl (Vbl i vc (During m)) is ij)
  = case M.lookup m sbind of
     Nothing -> fail ("lookupVarBind: Subscript ''"++m++"'' not found.")
     Just n ->
       let dn = During n in
       case M.lookup (i,vc,is,ij) lbind of
         Nothing       ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
         Just (BL vl)  ->  return $ BindList  $ map   (unGVar dn) vl
         Just (BS vs)  ->  return $ BindSet   $ S.map (unGVar dn) vs
         Just (BX tlvl)
           ->  return $ BindTLVs $ map (unTL dn) tlvl

lookupLstBind (BD (_,_,lbind)) lv@(LVbl (Vbl i vc vw) is ij)
  = case M.lookup (i,vc,is,ij) lbind of
     Nothing         ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
     Just (BL vl)  ->  return $ BindList  $ map   (unGVar vw) vl
     Just (BS vs)  ->  return $ BindSet   $ S.map (unGVar vw) vs
     Just (BX tlvl)
       ->  return $ BindTLVs $map  (unTL vw) tlvl
\end{code}

\newpage
\subsection{Derived Binding Functions}

Binding a list of list-variables to the null list:
\begin{code}
bindLVarsToNull bind [] = return bind
bindLVarsToNull bind (lv:lvs)
 = do bind' <- bindLVarToVList lv [] bind
      bindLVarsToNull bind' lvs
\end{code}

Binding a list of list-variables to the empty set:
\begin{code}
bindLVarsToEmpty bind [] = return bind
bindLVarsToEmpty bind (lv:lvs)
 = do bind' <- bindLVarToVSet lv S.empty bind
      bindLVarsToEmpty bind' lvs
\end{code}

\subsection{Mapped Variables}

We want to explicitly return all the variables that have been bound.
\begin{code}
mappedVars :: Binding -> VarSet
mappedVars (BD (vbind,sbind,lbind))
  = let domV  = M.keysSet vbind
        domS  = M.keysSet sbind
        whens = Static:Before:After:Textual:(map During $ S.toList domS)
        domL  = M.keysSet lbind
    in (S.map StdVar $ S.unions $ S.map (allVWhen whens) domV)
       `S.union`
       (S.map LstVar $ S.unions $ S.map (allLVWhen whens) domL)

allVWhen :: [VarWhen] -> (Identifier,VarClass) -> Set Variable
allVWhen whens (i,vc)  =  S.fromList $ map (Vbl i vc) whens

allLVWhen :: [VarWhen] -> ListVarKey -> Set ListVar
allLVWhen whens (i,vc,is,ij)
  = S.fromList $ map (lvbl is ij . Vbl i vc) whens
  where lvbl is ij v = LVbl v is ij
\end{code}

\newpage
\subsubsection{Finding Unbound Replacement Variables}

\begin{code}
findUnboundVars :: Binding -> Term -> VarSet
findUnboundVars bind trm  =  mentionedVars trm S.\\ mappedVars bind
\end{code}

\subsubsection{Instantiate Unbound Known Variables}

\begin{code}
bindKnown :: MonadFail m => [VarTable] -> Binding -> Term -> m Binding
bindKnown vts bind trm
 = do let unbound  =  findUnboundVars bind trm
      mkKnownBindings vts unbound bind
\end{code}

\textbf{We need to careful here.
Known list-variables may have ``less'' components
that are themselves bound}
\begin{code}
mkKnownBindings :: MonadFail m => [VarTable] -> VarSet -> Binding -> m Binding
mkKnownBindings vts unbound bind
  = mkKBs vts bind $ S.toList unbound
  where
    mkKBs vts bind [] = return bind
    mkKBs vts bind (gv:gvs)
      = do bind' <- mkKnownBind bind vts gv
           mkKBs vts (bind `mergeBindings` bind') gvs

mkKnownBind :: MonadFail m => Binding -> [VarTable] -> GenVar -> m Binding
mkKnownBind bind vts gv
 | isUnknownGVar vts gv  =  return emptyBinding
 | isLstV gv             =  mkKnownLstVarBind bind $ theLstVar gv
 | otherwise             =  bindGVarToGVar gv gv emptyBinding

mkKnownLstVarBind :: MonadFail m => Binding -> ListVar -> m Binding
mkKnownLstVarBind bind lv@(LVbl v@(Vbl _ vc vw) is js)
  = case bindLVarToVList lv [LstVar lv'] emptyBinding of
      Yes bind' -> return bind'
      But msgs -> fail (unlines ("mkKLVB error":msgs++moremsgs))
  where
    (is',js') = instLess bind vc vw is js
    lv' = LVbl v is' js'
    moremsgs = [ "is = "++show is
               , "js = "++show js
               , "is' = "++show is'
               , "js' = "++show js'
               ]

instLess :: Binding -> VarClass -> VarWhen -> [Identifier] -> [Identifier]
         -> ([Identifier],[Identifier])
instLess bind vc vw is js
  =  instLVIds bind vc vw (map (instId bind vc vw) is) [] js

instId bind vc vw i
  = case lookupVarBind bind (Vbl i vc vw) of
      Just (BI i')            ->  i'
      Just (BV (Vbl i' _ _))  ->  i'
      _                       ->  i

instLVIds bind vc vw si sj [] = (reverse si, reverse sj)
instLVIds bind vc vw si sj (j:js)
  = case lookupLstBind bind (LVbl (Vbl j vc vw) [] []) of
      Just (BL vl) -> instLVIds' bind vc vw si sj js $ idsOf vl
      Just (BS vs) -> instLVIds' bind vc vw si sj js $ idsOf $ S.toList vs
      _            -> instLVIds bind vc vw si (j:sj) js
  where
    instLVIds' bind vc vw si sj js (is',js')
      = instLVIds bind vc vw (reverse is'++si) (reverse js'++sj) js
\end{code}


\subsubsection{Collect Substitution List-Variable Pairings}

\begin{code}
termLVarPairings :: Term -> [(ListVar,ListVar)]
termLVarPairings (Sub _ tm s)     =  nub ( termLVarPairings tm
                                           ++ substLVarPairings s )
termLVarPairings (Cons _ _ _ ts)  =  nub $ concat $ map termLVarPairings ts
termLVarPairings (Bnd _ _ _ tm)   =  termLVarPairings tm
termLVarPairings (Lam _ _ _ tm)   =  termLVarPairings tm
termLVarPairings (Cls _ tm)       =  termLVarPairings tm
termLVarPairings _                =  []

substLVarPairings :: Substn -> [(ListVar,ListVar)]
substLVarPairings (LVarSub lvs) = S.toList lvs
\end{code}

Given that we can have substitutions of the form
$P[\lst y/\lst x][\lst e/\lst y]$
what we want is an relation saying
that $\setof{\lst e,\lst x,\lst y}$ are equivalent.
We can represent such a relation as a set of list-variable
sets.

\newpage
The following code is very general and should live elsewhere
\begin{code}
addToEquivClass :: Eq a => (a,a) -> [[a]] -> [[a]]
-- invariant, given eqvcs = [eqvc1,eqvc2,...]
--  z `elem` eqcvi ==> not( z `elem` eqcvj), for any j /= i
addToEquivClass (x,y) [] =  [nub[x,y]]
addToEquivClass (x,y) eqvcs
  = ([x,y] `union` hasX `union` hasY):noXY
  where
    (hasX,hasY,noXY) = findEquivClasses x y [] [] [] eqvcs

findEquivClasses
  :: Eq a  =>  a -> a       -- x and y
           ->  [a] -> [a]   -- accumulators for hasX, hasY
           ->  [[a]]        -- accumulator for noXY
           ->  [[a]]        -- equivalence classes under consideration
           ->  ([a],[a],[[a]])
findEquivClasses _ _ hasX hasY noXY [] = (hasX,hasY,noXY)
findEquivClasses x y hasX hasY noXY (eqvc:eqvcs)
  = checkX hasX hasY noXY
  where
    checkX hasX hasY noXY
      | x `elem` eqvc  =  checkY eqvc hasY noXY True
      | otherwise      =  checkY hasX hasY noXY False
    checkY hasX hasY noXY hadX
      | y `elem` eqvc  =  findEquivClasses x y hasX eqvc noXY eqvcs
      | hadX           =  findEquivClasses x y hasX hasY noXY eqvcs
      | otherwise      =  findEquivClasses x y hasX hasY (eqvc:noXY) eqvcs
\end{code}

Given a list of tuples, construct the equivalence classes:
\begin{code}
mkEquivClasses :: Eq a => [(a,a)] -> [[a]]
mkEquivClasses [] = []
mkEquivClasses (p:ps) = addToEquivClass p $ mkEquivClasses ps
\end{code}

Given equivalence classes,
which one, if any, does a value belong to?
\begin{code}
lookupEquivClasses :: Eq a => a -> [[a]] -> [a]
lookupEquivClasses x []  =  []
lookupEquivClasses x (eqvc:eqvcs)
 | x `elem` eqvc         =  eqvc \\ [x]
 | otherwise             =  lookupEquivClasses x eqvcs
\end{code}

\newpage


\textbf{
Function \texttt{mkFloatingBinding} needs
details regarding all substitution list-variable pairs
in order to produce valid bindings.
In particular, if an unbound substitution list-variable
is paired with a bound one, then the unknown one must be bound
to something of the same size as its bound partner, otherwise instantiation will
fail when it calls \texttt{substn}.
}
\begin{code}
mkFloatingBinding :: [VarTable] -> Binding -> [[ListVar]] -> VarSet -> Binding
mkFloatingBinding vts bind substEqv vs
  = qB emptyBinding $ S.toList vs
  where

    qB bind [] = bind
    qB bind ((StdVar v) :vl)
      | isUnknownVar vts v    =  qB (qVB bind v)   vl
    qB bind ((LstVar lv):vl)
      | isUnknownLVar vts lv  =  qB (qLVB bind lv) vl
    qB bind (_:vl)            =  qB bind           vl

    qVB bind v@(Vbl i vc vw)
      = case lookupVarTables vts v of
          UnknownVar  ->  fromJust $ bindVarToVar v (Vbl (fI i) vc vw) bind
          _           ->  fromJust $ bindVarToVar v v                  bind
      where qi = fI i

    qLVB bind lv@(LVbl v _ _)
      = case lookupLVarTables vts v of
          UnknownListVar  ->  qLVB' bind lv
          _               ->  fromJust $ bindLVarToSSelf lv bind

    -- UnknownListVar lv
    qLVB' bind lv@(LVbl (Vbl i _ _) _ _)
      | null lvEquivs
          = fromJust
              $ bindLVarToVList lv [floatingLV lv i] bind
      | otherwise
         = case bindSizes of
             [] -> fromJust
                      $ bindLVarToVList lv
                          [floatingLV lv i] bind
             [0] -> fromJust $ bindLVarToVList lv [] bind
             [1] -> fromJust
                      $ bindLVarToVList lv
                          [floatingLV lv i] bind
             [n] -> fromJust
                      $ bindLVarToVList lv
                          (map (floatingLV lv . fIn i) [1..n]) bind
             bs -> error $ unlines
                    ["mkFloatingBinding : equiv class has multiple sizes"
                    ,"bs="++show bs
                    ,"lv="++show lv
                    ]
      where
        lvEquivs = lookupEquivClasses lv substEqv
        bindSizes = equivBindingsSizes bind lvEquivs
        floatingLV lv@(LVbl (Vbl _ vc vw) is js) i
                 = LstVar (LVbl (Vbl (fI i) vc vw) is js)
\end{code}

Look up cardinalities of bindings of equivalences.
\textbf{Issue: what if their cardinality varies?}
\begin{code}
equivBindingsSizes :: Binding -> [ListVar] -> [Int]
equivBindingsSizes bind [] = []
equivBindingsSizes bind (lv:lvs)
  = case lookupLstBind bind lv of
       Nothing  ->  equivBindingsSizes bind lvs
       Just (BindList vl)  ->  nub (length vl : equivBindingsSizes bind lvs)
       Just (BindSet vs)   ->  nub (S.size vs : equivBindingsSizes bind lvs)
       Just (BindTLVs tlvl)
         | null tl    ->  nub (length vl : equivBindingsSizes bind lvs)
         | otherwise  ->  fail $ unlines
                           ["equivBindingsSizes: cannot handle BX with terms"
                           ,"tlvl="++show tlvl
                           ,"bind="++show bind
                           ]
         where (tl,vl) = (tmsOf tlvl, lvsOf tlvl)
\end{code}
Another issue, what if some are unbound? Ignore for now.

\subsubsection{Floating Instantiation}

\begin{code}
bindFloating :: (Monad m, MonadFail m) => [VarTable] -> Binding -> Term -> m Binding
bindFloating vts bind trm
 = return abind
 where
   unbound  =  findUnboundVars bind trm
   lvpairs  =  termLVarPairings trm
   substEquiv = mkEquivClasses lvpairs
   fbind    =  mkFloatingBinding vts bind substEquiv unbound
   abind    =  mergeBindings bind fbind
\end{code}


\subsection{Generating Fresh Variables}

We may need to generate fresh variables to discharge
freshness side-conditions.
\begin{code}
generateFreshVars :: VarSet -> VarSet -> Binding -> (Binding, VarSet)
generateFreshVars knownVs unfreshVs bind
  = genFresh knownVs bind S.empty $ S.toList unfreshVs

genFresh :: VarSet   -- existing variables
         -> Binding  -- binding (initial, evolving)
         -> VarSet   -- new variables
         -> [GenVar] -- to be made fresh
         -> (Binding, VarSet)
genFresh _ bind fresh []  =  (bind, fresh)
genFresh free bind fresh (gv:gvs)
  =  genFresh free' bind' fresh' gvs
  where
    -- remove floating mark from identifier
    fgv' = genFreshGVar free 1 $ sinkGV gv
    fgv's = S.singleton fgv'
    free' = free `S.union` fgv's
    bind' = fromJust (bindGVarToGVar gv fgv' emptyBinding)
            `mergeBindings` bind
    fresh' = fresh `S.union` fgv's

genFreshGVar :: VarSet -> Int -> GenVar -> GenVar
genFreshGVar free i gv
  | gv' `S.member` free  =  genFreshGVar free (i+1) gv
  | otherwise            =  gv'
  where gv'  =  remakeGVar i gv

remakeGVar i (StdVar v)   =  StdVar $ remakeVar   i v
remakeGVar i (LstVar lv)  =  LstVar $ remakeLVar  i lv
\end{code}


If \texttt{VarWhen} is not \texttt{During},
we change the identifier by appending the smallest natural number
that means it does not appear in \texttt{free}.
If \texttt{During}, then the subscript is the smallest natural making it unique.
\begin{code}
remakeVar i v@(Vbl n vc (During _))  =  Vbl n vc (During $ show i)
remakeVar i v@(Vbl (Identifier n _) vc vw)
                                     =  Vbl (fromJust $ ident (n++show i)) vc vw

remakeLVar i lv@(LVbl v is ij) = LVbl (remakeVar i v) is ij
\end{code}


\newpage
\subsection{Binding Dump}

Sometimes it is useful to dump all the binding results.
\begin{code}
dumpBinding :: Binding
            -> ( [ ( (Identifier,VarClass), VarBind )    ]
               , [ ( Subscript,             Subscript )  ]
               , [ ( ListVarKey,            LstVarBind ) ]
               )
dumpBinding (BD (vbind,sbind,lbind))
  = ( M.toList vbind
    , M.toList sbind
    , M.toList lbind
    )
\end{code}

\newpage
\subsubsection{Bijective Bindings}

For $\alpha$-equivalence testing in particular,
we need to know if a binding is bijective.
Each domain elements maps to a unique element of the same ``shape''.
\begin{code}
isBijectiveBinding :: Binding -> Bool
isBijectiveBinding = isBijectiveDump . dumpBinding
\end{code}

\begin{code}
isBijectiveDump :: ( [ ( (Identifier,VarClass), VarBind )    ]
                   , [ ( Subscript,             Subscript )  ]
                   , [ ( ListVarKey,            LstVarBind ) ] )
                -> Bool
\end{code}

We have (abstracting somewhat):
\begin{eqnarray*}
   vbind &:& V \fun I + V + T
\\ sbind &:& S \fun S
\\ lbind &:& LV \fun GV^* +  \Set GV + (LV + T)^*
\end{eqnarray*}
\begin{code}
isBijectiveDump (vbind,sbind,lbind)
  = isBijectiveVarBinding vbind &&
    isBijectiveAssocList sbind &&
    isBijectiveLstVarBind lbind
\end{code}


\begin{eqnarray*}
   vbind &:& V \fun I + V + T
\end{eqnarray*}
We require $vbind$ to actually be $V \fun V$,
and bijective.
\begin{code}
isBijectiveVarBinding vbind
  = case coerceAssocList varBind2Var vbind of
      Nothing  ->  False
      Just vvbind  ->  isBijectiveAssocList vvbind

varBind2Var (BV v)  =  return v
varBind2Var _  =  fail "VarBind not variable"
\end{code}

\begin{eqnarray*}
   lbind &:& LV \fun GV^* +  \Set GV + (LV + T)^*
\end{eqnarray*}
We require $lbind$ to actually be $LV \fun LV$
(singleton set/list),
and bijective.
\begin{code}
isBijectiveLstVarBind lbind
  = case coerceAssocList lstVarBind2LVar lbind of
      Nothing  ->  False
      Just lvlvbind  ->  isBijectiveAssocList lvlvbind

lstVarBind2LVar (BS vs)
  = case S.toList vs of
      [LstVar lv]  ->  return lv
      _            ->  fail "LstVarBind not a single list-variable"
lstVarBind2LVar (BL [LstVar lv])  =  return lv
lstVarBind2LVar (BX [Left lv])    =  return lv
lstVarBind2LVar _   =  fail "LstVarBind not a single list-variable"
\end{code}

\newpage
Coerce an association list to the expected form:
\begin{code}
coerceAssocList :: (Monad m, MonadFail m) => (b -> m c) -> [(a,b)] -> m [(a,c)]
coerceAssocList _ [] = return []
coerceAssocList coerce ((a,b):abs)
  = do c <- coerce b
       acs <- coerceAssocList coerce abs
       return ((a,c):acs)
\end{code}

Simple test for bijectivity, suitable for use with Binding components,
given that they are in fact of type \texttt{Map a b}.
\begin{code}
isBijectiveAssocList :: (Ord a, Ord b) => [(a,b)] -> Bool
isBijectiveAssocList assoc
  =  cardAs == cardBs
  where
    (as,bs) = unzip assoc
    cardAs = S.size $ S.fromList as
    cardBs = S.size $ S.fromList bs
\end{code}

\subsubsection{Trivial Quantifiers}

A quantifier match is trivial if all its list-variables
are bound to empty sets or lists.

\begin{code}
onlyTrivialQuantifiers :: Binding -> Bool
onlyTrivialQuantifiers (BD (_,_,lbind))
  | null lvbinds  =  False
  | otherwise     =  all trivialListVarBind lvbinds
  where lvbinds = M.elems lbind

trivialListVarBind :: LstVarBind -> Bool
trivialListVarBind (BL vl)   =  null vl
trivialListVarBind (BS vs)   =  S.null vs
trivialListVarBind (BX vts)  =  null vts
\end{code}

\newpage
\subsection{Binding Patches}

In a few cases we want to replace a given range element of a binding
with something else.
The main use is when floating variables are being replaced by actual terms
or variable-list,
when a match is being applied.

\begin{code}
patchVarBind :: Variable -> Term -> Binding -> Binding
patchVarBind v t (BD (vbind,sbind,lbind)) = BD (vbind',sbind,lbind)
 where
   vbind' = M.mapWithKey f vbind
   f _ (BV v') | v == v'  =  term2VarBind t
   f _ bv                 =  bv

term2VarBind (Var _ v)  =  BV v
term2VarBind t          =  BT t
\end{code}

\begin{code}
patchVarListBind :: ListVar -> VarList -> Binding -> Binding
patchVarListBind lv vl (BD (vbind,sbind,lbind)) = BD (vbind,sbind,lbind')
  where
    lbind' = M.mapWithKey f lbind
    f _ (BL [LstVar lv']) | lv == lv'  =  BL vl
    f _ blv                            =  blv
\end{code}

\newpage
\subsection{Binding Internal Tests}

\begin{code}
int_tst_Binding :: [TF.Test]
int_tst_Binding
 = [ testGroup "\nBinding Internal:"
     [ tst_bind_VarToVar
     , tst_bind_VarToTerm
     ]
   ]
\end{code}

\begin{code}
tst_bind_VarToVar :: TF.Test

-- naming convention ct<varname>
-- c = o (ObsV), e (ExprV), p (PredV)
-- t = s (Static), b (Before), d (During), a (After), t (Textual)

g = fromJust $ ident "g"
osg = ObsVar (fromJust $ ident "g") Static
osin = ObsVar (fromJust $ ident "in") Static
osout = ObsVar (fromJust $ ident "out") Static

_m = During "m" ; _n = During "n"

v = fromJust $ ident "v"
obv = ObsVar v Before ; oav = ObsVar v After ; otv = ObsVar v Textual
odv = ObsVar v (During "") ; odvm = ObsVar v _m
x = fromJust $ ident "x"
obx = ObsVar x Before  ; oax = ObsVar x After ; otx = ObsVar x Textual
odx = ObsVar x (During "")
odxm = ObsVar x _m ; odxn = ObsVar x _n

tst_bind_VarToVar
 = testGroup "bind Var to Var"
    [ testCase "Obs-Static g |-> in -- should succeed"
        ( bindVarToVar osg osin emptyBinding
          @?= Just (BD (M.fromList [((g,ObsV),BV osin)], M.empty, M.empty)) )
    , testCase "Obs-Before v |-> x -- should succeed"
        ( bindVarToVar obv obx emptyBinding
          @?= Just (BD (M.fromList [((v,ObsV),BI x)], M.empty, M.empty)) )
    , testCase "Obs-During v_m |-> x_m -- should succeed"
        ( bindVarToVar odvm odxm emptyBinding
          @?= Just (BD (M.fromList [((v,ObsV),BI x)],
                       (M.fromList [("m","m")]), M.empty)) )
    , testCase "Obs-During v_m |-> x_n -- should succeed"
        ( bindVarToVar odvm odxn emptyBinding
          @?= Just (BD (M.fromList [((v,ObsV),BI x)],
                       (M.fromList [("m","n")]), M.empty)) )
    , testCase "Obs-Before-During v ; v_m |-> x ; x_n -- should succeed"
        ( ( bindVarToVar odvm odxn $ fromJust
          $ bindVarToVar obv obx emptyBinding )
          @?= Just (BD (M.fromList [((v,ObsV),BI x)],
                       (M.fromList [("m","n")]), M.empty)) )
    , testCase "Obs-During conflict v_m ; v_m |-> x_n ; x_m -- should fail"
        ( ( bindVarToVar odvm odxm $ fromJust
          $ bindVarToVar odvm odxn emptyBinding )
          @?= Nothing )
    , testCase "Static conflict  g,g |-> in,out -- should fail"
        ( ( bindVarToVar osg osin $
                         fromJust $ bindVarToVar osg osout $ emptyBinding )
           @?= Nothing )
    ]

tstBVV = defaultMain [tst_bind_VarToVar]
\end{code}

\newpage
\begin{code}
tst_bind_VarToTerm :: TF.Test

int  = GivenType $ fromJust $ ident "Z"
tInt = E int
mkV v = fromJust $ var tInt v
n_add = fromJust $ ident "add"

eadd v1 v2 = Cons tInt True n_add [mkV v1, mkV v2]
bradd vw v1 v2 = unTerm vw $ eadd v1 v2

u = fromJust $ ident "u"
obu = ObsVar v Before ; oau = ObsVar v After ; otu = ObsVar v Textual
odu = ObsVar v (During "") ; odum = ObsVar v _m
y = fromJust $ ident "y"
oby = ObsVar v Before ; oay = ObsVar v After ; otyu = ObsVar v Textual
ody = ObsVar v (During "") ; odym = ObsVar v _m
odyn = ObsVar v _n

xy = eadd obx oby ; x'y' = eadd oax oay ; xy' = eadd obx oay
uv = eadd obu obv ; u'v' = eadd oau oav

xmym = bradd _m obx oby
xnyn = bradd _n obx oby
xmyn = eadd odxm odyn ;
e = fromJust $ ident "e"
ebe = ExprVar e Before ; eae = ExprVar e After
edem = ExprVar e $ _m ; eden = ExprVar e $ _n

tst_bind_VarToTerm
 = testGroup "bind Var to Term"
    [ testCase "Obs-Static g |-> x+y -- should succeed"
      ( bindVarToTerm osg xy emptyBinding
        @?=
        Just (BD (M.fromList [((g,ObsV),BT xy)], M.empty, M.empty)) )
    , testCase "Obs-Static g |-> x'+y' -- should succeed"
      ( bindVarToTerm osg x'y' emptyBinding
        @?=
        Just (BD (M.fromList [((g,ObsV),BT x'y')], M.empty, M.empty)) )
    , testCase "Obs-Static g |-> x+y' -- should succeed"
      ( bindVarToTerm osg xy' emptyBinding
        @?=
        Just (BD (M.fromList [((g,ObsV),BT xy')], M.empty, M.empty)) )
    , testCase "Expr-Before e |-> x+y -- should succeed"
      ( bindVarToTerm ebe xy emptyBinding
        @?=
        Just (BD (M.fromList [((e,ExprV),BT xy)], M.empty, M.empty)) )
    , testCase "Expr-During em |-> x_m+y_m -- should succeed"
      ( bindVarToTerm edem xmym emptyBinding
        @?=
        Just (BD (M.fromList [((e,ExprV),BT xy)],
                 (M.fromList [("m","m")]), M.empty)) )
    , testCase "Expr-During em |-> x_n+y_n -- should succeed"
      ( bindVarToTerm edem xnyn emptyBinding
        @?=
        Just (BD (M.fromList [((e,ExprV),BT xy)],
                 (M.fromList [("m","n")]), M.empty)) )
    , testCase "Expr-After e' |-> x'+y' -- should succeed"
      ( bindVarToTerm eae x'y' emptyBinding
        @?=
        Just (BD (M.fromList [((e,ExprV),BT xy)], M.empty, M.empty)) )
    , testCase "em |-> x_n+y_n onto previous x'+y'-- should succeed"
      ( ( bindVarToTerm edem xnyn $
          BD (M.fromList [((e,ExprV),BT xy)], M.empty, M.empty) )
        @?=
        Just (BD ( M.fromList [((e,ExprV),BT xy)],
                   M.fromList [("m","n")], M.empty)) )
    , testCase "e' |-> x'+y' onto previous xn+yn-- should succeed"
      ( ( bindVarToTerm eae x'y' $
          BD (M.fromList [((e,ExprV),BT xy)],
              M.fromList [("m","n")], M.empty) )
        @?=
        Just (BD ( M.fromList [((e,ExprV),BT xy)]
                 , M.fromList [("m","n")], M.empty) ) )
    , testCase "e' |-> x'+y' ; em |-> x_n+y_n -- should succeed"
      ( ( bindVarToTerm edem xnyn $ fromJust
          $ bindVarToTerm eae x'y' emptyBinding )
        @?=
        Just (BD (M.fromList [((e,ExprV),BT xy)],
                  M.fromList [("m","n")], M.empty)) )

    -- all subsequent bind attempts should fail
    , testCase "Obs-Before v |-> x+y -- should fail"
      ( bindVarToTerm obv xy emptyBinding @?= Nothing )
    , testCase "Expr-Before e |-> x+y' -- should fail"
      ( bindVarToTerm ebe xy' emptyBinding @?= Nothing )
    , testCase "Expr-Before e |-> x'+y' -- should fail"
      ( bindVarToTerm ebe x'y' emptyBinding @?= Nothing )
    , testCase "Expr-After e' |-> x+y -- should fail"
      ( bindVarToTerm eae xy emptyBinding @?= Nothing )
    , testCase "Expr-After e' |-> x+y' -- should fail"
      ( bindVarToTerm eae xy' emptyBinding @?= Nothing )
    , testCase "Expr-During em |-> x_m+y_n -- should fail"
      ( bindVarToTerm edem xmyn emptyBinding @?= Nothing )
    ]

tstBVT = defaultMain [tst_bind_VarToTerm]
\end{code}

\begin{code}
tstBind = defaultMain int_tst_Binding
\end{code}
