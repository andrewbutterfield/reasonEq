\section{Binding}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Binding
( VarBind(..), pattern BindId, pattern BindVar, pattern BindTerm
, LstVarBind(..), pattern BindList, pattern BindSet, pattern BindTerms
, Binding
, emptyBinding
, bindVarToVar
, bindVarToTerm
, bindLVarToVList
, bindLVarToVSet
, bindLVarToTList
, bindGVarToGVar
, bindGVarToVList
, bindGVarToTList
, lookupBind
, lookupLstBind
, int_tst_Binding
) where
import Data.Maybe (fromJust)
import Data.List (nub)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

import Utilities
import LexBase
import Variables
import AST
import VarData
\end{code}

\subsection{Introduction}

Bindings are the result of matching,
mapping pattern variables to corresponding candidate variables or terms.
From the outside a binding has two mappings:
\begin{itemize}
  \item \texttt{Variable} to \texttt{Variable} or \texttt{Term}.
  \item \texttt{ListVar} to \texttt{VarList} or \texttt{VarSet} or \texttt{[Term]}.
\end{itemize}
However,
we have a number of constraints regarding compatibilty
between pattern variables  and their corresponding candidate bindings,
based on variable class and temporality.

Basically observation variables can be bound to both observation
and expression variables,
while expression and predicate variables can only be bound to
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
       \texttt{ObsV} & Yes & No &  No
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
validVarClassBinding ExprV ExprV  =  True
validVarClassBinding PredV PredV  =  True
validVarClassBinding _     _      =  False
\end{code}
A similar predicate for binding to terms:
\begin{code}
validVarTermBinding :: VarClass -> TermKind -> Bool
validVarTermBinding ObsV  (E _)  =  True
validVarTermBinding ObsV  (E _)  =  True
validVarTermBinding ExprV (E _)  =  True
validVarTermBinding PredV P      =  True
validVarTermBinding _     _      =  False
\end{code}

As far as temporality goes,
Static can bind to anything except Textual,
Textual can only bind to Textual \emph{variables},
and other dynamics can only bind to the same temporality
(Fig. \ref{fig:utp-perm-time-bind}).
\begin{figure}
  \begin{center}
    \begin{tabular}{|c|c|l|}
      \hline
      pattern && allowed candidates
    \\\hline
       \texttt{Static}
       &$\mapsto$&
       \texttt{Static}, \texttt{Before}, \texttt{During}, \texttt{After}
    \\\hline
       $d$ &$\mapsto$&
       $d$, for $d$ in
       \texttt{Before}, \texttt{During}, \texttt{After}, \texttt{Textual}
    \\\hline
    \end{tabular}
  \caption{Permissible variable temporality binding combinations. }
  \label{fig:utp-perm-time-bind}
  \end{center}
\end{figure}
\begin{code}
validVarTimeBinding :: VarWhen -> VarWhen -> Bool
validVarTimeBinding Static Textual  =  False
validVarTimeBinding Static _        =  True
validVarTimeBinding pwhen  cwhen    =  pwhen == cwhen
\end{code}
In a scenario where $a$ binds to $b$,
if $a$ is dynamic,
then binding respects temporality
($a \mapsto b, a' \mapsto b', a_m \mapsto b_n, \texttt{a} \mapsto \texttt{b}$).
Also any one of those bindings induces all the others.

The following scenario (Fig. \ref{fig:utp-dynamic-inducing})
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
The key issue here is how each single binding inserted,
of a given temporality,
also induces bindings for the same variable identifiers,
but with as many other temporalities as is possible.
From all of this we can see that we need to record
identifier-identifier bindings along with subscript-subscript bindings,
for dynamic variables,
and identifier to variable bindings for static variables.
Given that similar rules apply to list variables,
we find that, in effect, we need to maintain three mappings:
\begin{description}
  \item[Variable to \dots]
    Mapping of variable identifier and class,
    to either variables or identifier and class or terms.
  \item[Subscript to \dots]
    Mapping of subscripts to subscripts.
  \item[List-Variable to \dots]
    Mapping of list-variable identifiers, class and identifier-lists,
    to lists of general variables, or terms.
\end{description}


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
pattern BindId   i  =  BI i
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
  \texttt{VarList} or \texttt{VarSet} or \texttt{[Term]}
}

We bind a list-variable to either a list or set of variables,
or a list of terms.
We use the variable identifier and the list of `subtracted` identifiers
as the map key.

\begin{code}
data LstVarBind
 = BL  VarList
 | BS  VarSet
 | BX  [Term]
 deriving (Eq, Ord, Show, Read)

type ListVarBinding = M.Map (Identifier,VarClass,[Identifier]) LstVarBind
\end{code}
We return just the variable list or set, or term-list from a lookup:
\begin{code}
pattern BindList  vl  =  BL vl
pattern BindSet   vs  =  BS vs
pattern BindTerms ts  =  BX ts
\end{code}

We put these together:
\begin{code}
newtype Binding = BD (VarBinding, SubBinding, ListVarBinding)
 deriving (Eq, Show, Read)

emptyBinding :: Binding
emptyBinding = BD (M.empty, M.empty, M.empty)
\end{code}

\newpage
\subsection{Binding Insertion}

If a variable is already present,
then the new binding must be the same,
otherwise we fail.

We have a generic insertion function as follows:
\begin{code}
insertDR :: (Ord d, Monad m)
         => String -> (r -> r -> Bool)
         -> d -> r -> Map d r
         -> m (Map d r)
insertDR nAPI rEqv d r bind
 = case M.lookup d bind of
     Nothing         ->  return $ M.insert d r bind
     Just r0
      | r `rEqv` r0  ->  return bind
      | otherwise    ->  fail (nAPI++": already bound differently.")
\end{code}

\subsubsection{Binding Variable to Variable}

\begin{code}
bindVarToVar :: Monad m => Variable -> Variable -> Binding -> m Binding
\end{code}


A \texttt{Static} variable can bind to
any non-\texttt{Textual} thing in the appropriate class.
\begin{code}
bindVarToVar (Vbl vi vc Static) x@(Vbl xi xc xw)
             (BD (vbind,sbind,lbind))
 | xw == Textual  =  fail "bindVarToVar: Static cannot bind to Textual"
 | validVarClassBinding vc xc
   =  do vbind' <- insertDR "bindVarToVar" (==) (vi,vc) (BV x) vbind
         return $ BD (vbind',sbind,lbind)
 | otherwise      =  fail "bindVarToVar: incompatible Static classes"
\end{code}

A \texttt{During} variable can only bind to a \texttt{During} variable
in the appropriate class.
\begin{code}
bindVarToVar (Vbl vi vc (During m)) x@(Vbl xi xc (During n))
             (BD (vbind,sbind,lbind))
 | validVarClassBinding vc xc
   =  do vbind' <- insertDR "bindVarToVar" (==) (vi,vc) (BI xi) vbind
         sbind' <- insertDR "bindVarToVar" (==) m n sbind
         return $ BD (vbind',sbind',lbind)
 | otherwise  =  fail "bindVarToVar: incompatible During classes"
\end{code}

A dynamic variable can only bind to a dynamic variable of the same
temporality in the appropriate class.
\begin{code}
bindVarToVar (Vbl  vi vc vw) (Vbl xi xc xw)
             (BD (vbind,sbind,lbind))
 | vw /= xw   =  fail "bindVarToVar: different temporalities"
 | validVarClassBinding vc xc
   =  do vbind' <- insertDR "bindVarToVar" (==) (vi,vc) (BI xi) vbind
         return $ BD (vbind',sbind,lbind)
 | otherwise  =  fail "bindVarToVar: incompatible variables"
\end{code}

\newpage

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
    Managing Dynamic binding coherence, where
    $s$ is \texttt{Static}, $\texttt{v}$ and $\texttt{x}$ are \texttt{Textual},
    and $v$ and $x$ with or without decoration, are any other \texttt{Dynamic},
    and $i_s$ and $i_v$ are the respective identifiers  underlying $s$ and the $v$s
  }
  \label{fig:dynamic-coherence}
\end{center}
\end{figure}

\newpage
\subsubsection{Binding Variable to Term}

An observation or expression variable can bind to an expression
while a predicate variable can only bind to a predicate.
\begin{code}
bindVarToTerm :: Monad m => Variable -> Term -> Binding -> m Binding
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
   = do vbind' <- insertDR "bindVarToTerm" (==) (vi,vc) (BT ct) vbind
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
   = do vbind' <- insertDR "bindVarToTerm(ev1)" (==) (vi,ExprV) (bterm ct) vbind
        return $ BD (vbind',sbind,lbind)
 | otherwise
   = case (vt,thectw) of
      (During m, During n) ->
          do vbind' <- insertDR "bindVarToTerm(ev2)" (==) (vi,ExprV) (bterm ct) vbind
             sbind' <- insertDR "bindVarToTerm(ev3)" (==) m n sbind
             return $ BD (vbind',sbind',lbind)
      _ | vt /= thectw     ->
            fail "bindVarToTerm: e.-var different temporality"
        | otherwise ->
            do vbind' <- insertDR "bindVarToTerm" (==) (vi,ExprV) (bterm ct) vbind
               return $ BD (vbind',sbind,lbind)
 where
   ctws = temporalityOf ct
   wsize = S.size ctws
   thectw = S.elemAt 0 ctws
\end{code}
Dynamic predicate variables can only bind to
predicate terms, all of whose dynamic variables have the same temporality.
\begin{code}
bindVarToTerm v@(Vbl vi PredV vt) ct (BD (vbind,sbind,lbind))
 | isExpr ct  =  fail "bindVarToTerm: p.-var. cannot bind expression."
 | wsize  > 1  =  fail "bindVarToTerm: p.-var. mixed term temporality."
 | wsize == 0  -- term has no variables
   = do vbind' <- insertDR "bindVarToTerm(pv1)" (==) (vi,PredV) (bterm ct) vbind
        return $ BD (vbind',sbind,lbind)
 | otherwise
   = case (vt,thectw) of
      (During m, During n) ->
          do vbind' <- insertDR "bindVarToTerm(pv2)" (==) (vi,PredV) (bterm ct) vbind
             sbind' <- insertDR "bindVarToTerm(pv3)" (==) m n sbind
             return $ BD (vbind',sbind',lbind)
      _ | vt /= thectw     ->
            fail "bindVarToTerm: p.-var different temporality"
        | otherwise ->
            do vbind' <- insertDR "bindVarToTerm" (==) (vi,PredV) (bterm ct) vbind
               return $ BD (vbind',sbind,lbind)
 where
   ctws = temporalityOf ct
   wsize = S.size ctws
   thectw = S.elemAt 0 ctws
\end{code}

Catch-all
\begin{code}
bindVarToTerm pv ct _
 = error $ unlines
     [ "bindVarToTerm: fell off end"
     , "pv = " ++ show pv
     , "ct = " ++ show ct ]
\end{code}

Determining the temporality of a term:
\begin{code}
temporalityOf :: Term -> Set VarWhen
temporalityOf t = termTmpr S.empty [] t

-- for now we process all variables in the same way,
-- regardless of whether their occurrence is free, binding or bound.
termTmpr vws ts (Var _ (Vbl _ _ vw))  =  termsTmpr (S.insert vw vws) ts
termTmpr vws ts (Cons _ _ ts')        =  termsTmpr vws (ts'++ts)
termTmpr vws ts (Bind _ _ vs t)       =  vlTmpr vws (t:ts) $ S.toList vs
termTmpr vws ts (Lam _ _ vl t)        =  vlTmpr vws (t:ts) vl
termTmpr vws ts (Sub _ t sub)         =  subTmpr   vws (t:ts) sub
termTmpr vws ts _                     =  termsTmpr vws ts

temporalitiesOf :: [Term] -> Set VarWhen
temporalitiesOf ts = termsTmpr S.empty ts

termsTmpr vws []      =  vws
termsTmpr vws (t:ts)  =  termTmpr vws ts t

vlTmpr vws ts []                                = termsTmpr vws ts
vlTmpr vws ts (StdVar (Vbl _ _ vw):lv)          = vlTmpr (S.insert vw vws) ts lv
vlTmpr vws ts (LstVar (LVbl (Vbl _ _ vw) _):lv) = vlTmpr (S.insert vw vws) ts lv

subTmpr vws ts (Substn tsub lvsub)  =  lvsubTmpr vws ts tsub $ S.toList lvsub

lvsubTmpr vws ts tsub []  =  tsubTmpr vws ts $ S.toList tsub
lvsubTmpr vws ts tsub ((LVbl (Vbl _ _ vw1) _,LVbl (Vbl _ _ vw2) _):lvsub)
 = lvsubTmpr (S.fromList [vw1,vw2] `S.union` vws) ts tsub lvsub

tsubTmpr vws ts tsub = let (vs,ts') = unzip tsub in vsTmpr vws (ts'++ts) vs

vsTmpr vws ts []                 =  termsTmpr vws ts
vsTmpr vws ts ((Vbl _ _ vw):vs)  =  vsTmpr (S.insert vw vws) ts vs
\end{code}

\newpage
When we store a dynamic term,
we ``normalise'' it by setting its temporality to \texttt{Before}.
\begin{code}
bterm :: Term -> VarBind
bterm t = BT $ bterm' t
bterm' v@(Var tk (Vbl vi vc vw))
  | vw == Static || vw == Textual || vw == Before  =  v
  | otherwise            =  btvar  tk $ Vbl vi vc Before
bterm' (Cons tk n ts)    =  Cons   tk n $ map bterm' ts
bterm' (Bind tk n vs t)  =  btbind tk n (S.map bgv vs) $ bterm' t
bterm' (Lam tk n vl t)   =  btlam  tk n (  map bgv vl) $ bterm' t
bterm' (Sub tk t sub)    =  Sub    tk (bterm' t) $ bsub sub
bterm' t                 =  t

bv v@(Vbl vi vc vw)
  | vw == Static || vw == Textual || vw == Before  =  v
  | otherwise                                      =  Vbl vi vc Before

blv (LVbl v is)  =  LVbl (bv v) is
bgv (StdVar v)   =  StdVar $ bv  v
bgv (LstVar lv)  =  LstVar $ blv lv

bsub (Substn tsub lvsub)
 = btsubst (btsub $ S.toList tsub) (blvsub $ S.toList lvsub)

btsub tsub = map bvt tsub ; bvt (v,t) = (bv v,bterm' t)
blvsub lvsub = map blvlv lvsub ; blvlv (lv1,lv2) = (blv lv1,blv lv2 )

btvar  tk       =  getJust "bterm var failed"  . var  tk
btbind tk n vl  =  getJust "bterm bind failed" . bind tk n vl
btlam  tk n vs  =  getJust "bterm lam failed"  . lam  tk n vs
btsubst tsub lvsub = getJust "" $ substn tsub lvsub
\end{code}



\newpage
\subsubsection{Binding List-Variables to Variable-Lists}

For list-variable binding we require all variables in the list
to have a class compatible with the list variable,
and to have the same temporality.
The exception is if the list-variable is static,
in which case we need to ensure that there are no textual variables present.
\begin{code}
validStaticGVarClass vc gvar
  = gvarWhen gvar /= Textual && validVarClassBinding vc (gvarClass gvar)

vlCompatible :: VarClass -> VarWhen -> VarList -> (Bool, VarWhen)
vlCompatible vc Static vl  =  (all (validStaticGVarClass vc) vl,Static)
vlCompatible vc vw     vl  =  vlComp vc vw S.empty vl

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

\newpage
\begin{code}
bindLVarToVList :: Monad m => ListVar -> VarList -> Binding -> m Binding
\end{code}

A Static list-variable binds to any list without \texttt{Textual} variables.
\begin{code}
bindLVarToVList lv@(LVbl (Vbl i vc Static) is) vl (BD (vbind,sbind,lbind))
 | valid
    =  do lbind' <- insertDR "bindLVarToVList(static)" (==) (i,vc,is) (BL vl) lbind
          return $ BD (vbind,sbind,lbind')
 | otherwise = fail "bindLVarToVList: static cannot bind to any textual."
 where
    (valid, vlw) = vlCompatible vc Static vl
\end{code}


A dynamic list-variable binds to any list of dynamic variables
all of which have the same class and temporality as itself.
\begin{code}
bindLVarToVList lv@(LVbl (Vbl i vc vw) is) vl (BD (vbind,sbind,lbind))
 | valid
   = case (vw,vlw) of
      (During m,During n) ->
            do lbind' <- insertDR "bindLVarToVList(dynamic)" (==)
                                  (i,vc,is) (BL vl) lbind
               sbind' <- insertDR "bindLVarToVList(subscript)" (==) m n sbind
               return $ BD (vbind,sbind',lbind')
      _ | vw == vlw       ->
            do lbind' <- insertDR "bindLVarToVList(static)" (==)
                                  (i,vc,is) (BL vl) lbind
               return $ BD (vbind,sbind,lbind')
        | otherwise       ->
            fail "bindLVarToVList: different temporality."
 | otherwise = fail "bindLVarToVList: incompatible dynamic temporality."
 where
   (valid, vlw) = vlCompatible vc vw vl
\end{code}

Anything else fails.
\begin{code}
bindLVarToVList _ _ _ = fail "bindLVarToVList: invalid lvar. -> vlist binding."
\end{code}

\newpage
\subsubsection{Binding List-Variables to Variable-Sets}

Similar code to \texttt{bindLVarToVList} above, except we have sets.
\begin{code}
vsCompatible vc Static vs  =  (all (validStaticGVarClass vc) vs, Static)
vsCompatible vc vw vs      =  vlComp vc vw S.empty (S.toList vs)
\end{code}

\begin{code}
bindLVarToVSet :: Monad m => ListVar -> VarSet -> Binding -> m Binding

bindLVarToVSet lv@(LVbl (Vbl i vc Static) is) vs (BD (vbind,sbind,lbind))
 | valid
    =  do lbind' <- insertDR "bindLVarToVSet(static)" (==) (i,vc,is) (BS vs) lbind
          return $ BD (vbind,sbind,lbind')
 | otherwise = fail "bindLVarToVSet: static cannot bind to any textual."
 where
    (valid, vsw) = vsCompatible vc Static vs

bindLVarToVSet lv@(LVbl (Vbl i vc vw) is) vs (BD (vbind,sbind,lbind))

 | valid
   = case (vw,vsw) of
      (During m,During n) ->
            do lbind' <- insertDR "bindLVarToVSet(dynamic)" (==)
                                  (i,vc,is) (BS vs) lbind
               sbind' <- insertDR "bindLVarToVSet(subscript)" (==) m n sbind
               return $ BD (vbind,sbind',lbind')
      _ | vw == vsw       ->
            do lbind' <- insertDR "bindLVarToVSet(static)" (==)
                                  (i,vc,is) (BS vs) lbind
               return $ BD (vbind,sbind,lbind')
        | otherwise       ->
            fail "bindLVarToVSet: different temporality."
 | otherwise = fail "bindLVarToVSet: incompatible dynamic temporality."
 where
   (valid, vsw) = vsCompatible vc vw vs

bindLVarToVSet _ _ _ = fail "bindLVarToVSet: invalid lvar. -> vset binding."
\end{code}

\newpage
\subsubsection{Binding List-Variables to Term-lists}

An observation or expression list-variable can bind to expressions
while a predicate list-variable can only bind to a predicates.
\begin{code}
bindLVarToTList :: Monad m => ListVar -> [Term] -> Binding -> m Binding
\end{code}


A \texttt{Textual} pattern variable cannot bind to a term
\begin{code}
bindLVarToTList (LVbl (Vbl _ _ Textual) _) _ binds
 = fail "bindLVarToTList: textual list-vars. not allowed."
\end{code}

Static patterns bind to anything in the appropriate class,
as per Fig.\ref{fig:utp-perm-class-bind}.
\begin{code}
bindLVarToTList (LVbl (Vbl vi vc Static) is) cts (BD (vbind,sbind,lbind))
 | all (validVarTermBinding vc) (map termkind cts)
    = do lbind' <- insertDR "bindLVarToTList(static)" (==)
                            (vi,vc,is) (BX cts) lbind
         return $ BD (vbind,sbind,lbind')
 | otherwise  =  fail "bindLVarToTList: incompatible variable and terms."
\end{code}

All remaining pattern cases are non-\texttt{Textual} dynamic variables.

Dynamic predicate list-variables can only bind to
predicate terms, all of whose dynamic variables have the same temporality.
Dynamic observable and expression list-variables can only bind to
expression terms, all of whose dynamic variables have the same temporality.
\begin{code}
bindLVarToTList (LVbl (Vbl vi vc vt) is) cts (BD (vbind,sbind,lbind))
 | vc == PredV && any isExpr cts
           =  fail "bindLVarToTList: pred. l-var. cannot bind to expression."
 | vc /= PredV && any isPred cts
           =  fail "bindLVarToTList: non-pred. l-var. cannot bind to predicate."
 | wsize  > 1  =  fail "bindLVarToTList: p.-var. mixed term temporality."
 | wsize == 0  -- term has no variables
   = do lbind' <- insertDR "bindLVarToTList(pv1)" (==) (vi,vc,is) (bterms cts) lbind
        return $ BD (vbind,sbind,lbind')
 | otherwise
   = case (vt,thectw) of
      (During m, During n) ->
          do lbind' <- insertDR "bindLVarToTList(plv2)" (==)
                                (vi,vc,is) (bterms cts) lbind
             sbind' <- insertDR "bindLVarToTList(plv3)" (==) m n sbind
             return $ BD (vbind,sbind',lbind')
      _ | vt /= thectw     ->
            fail "bindLVarToTList: p.-var different temporality"
        | otherwise ->
            do lbind' <- insertDR "bindLVarToTList(plv4)" (==)
                                  (vi,vc,is) (bterms cts) lbind
               return $ BD (vbind,sbind,lbind')
 where
   ctws = temporalitiesOf cts
   wsize = S.size ctws
   thectw = S.elemAt 0 ctws
\end{code}

Catch-all
\begin{code}
bindLVarToTList plv cts _
 = error $ unlines
     [ "bindLVarToTList: fell off end"
     , "plv = " ++ show plv
     , "cts = " ++ show cts ]
\end{code}

We need to normalise lists of terms:
\begin{code}
bterms :: [Term] -> LstVarBind
bterms ts = BX $ map bterm' ts
\end{code}
\newpage

\subsubsection{Binding General-Variables to General-Variables}

An list-variable can bind to a singleton list of any general variable,
while a standard-variable can only bind to a standard variable.
\begin{code}
bindGVarToGVar :: Monad m => GenVar -> GenVar -> Binding -> m Binding
bindGVarToGVar (LstVar lv) gv binds = bindLVarToVList lv [gv] binds
bindGVarToGVar (StdVar pv) (StdVar cv) binds = bindVarToVar pv cv binds
bindGVarToGVar _ _ _ = fail "bindGVarToGVar: invalid stdvar. -> lstvar. binding."
\end{code}

\subsubsection{Binding General-Variables to Variable-Lists}

An list-variable can bind to a list of any length,
while a standard-variable can only bind to the standard variable inside
a singleton list.
\begin{code}
bindGVarToVList :: Monad m => GenVar -> VarList -> Binding -> m Binding
bindGVarToVList (LstVar lv) vl binds = bindLVarToVList lv vl binds
bindGVarToVList (StdVar pv) [StdVar cv] binds = bindVarToVar pv cv binds
bindGVarToVList _ _ _ = fail "bindGVarToVList: invalid gvar. -> vlist binding."
\end{code}

\subsubsection{Binding General-Variables to Term-Lists}

An list-variable can bind to a list of any length,
while a standard-variable can only bind to the standard variable inside
a singleton list.
\begin{code}
bindGVarToTList :: Monad m => GenVar -> [Term] -> Binding -> m Binding
bindGVarToTList (LstVar lv) ts binds = bindLVarToTList lv ts binds
bindGVarToTList (StdVar pv) [t] binds = bindVarToTerm pv t binds
bindGVarToTList _ _ _ = fail "bindGVarToVList: invalid gvar. -> vlist binding."
\end{code}

\newpage
\subsection{Binding Lookup}

Binding lookup is very straightforward,
with the minor wrinkle that we need to ensure we lookup
the subscript binding if the lookup variable has \texttt{During} temporality.
\begin{code}
lookupBind :: Monad m => Binding -> Variable -> m VarBind
lookupBind (BD (vbind,_,_)) v@(Vbl vi vc Static)
  = case M.lookup (vi,vc) vbind of
      Nothing  ->  fail ("lookupBind: Variable "++show v++" not found.")
      Just (BI xi) -> error $ unlines
                       [ "lookupBind: Static bound to (BI xi)"
                       , "v = " ++ show v
                       , "xi = " ++ show xi
                       , "vbind:\n" ++ show vbind
                       ]
      Just vb  ->  return vb

lookupBind (BD (vbind,sbind,_)) v@(Vbl vi vc (During m))
  = case M.lookup m sbind of
     Nothing -> fail ("lookupBind: Subscript ''"++m++"'' not found.")
     Just n ->
       case M.lookup (vi,vc) vbind of
         Nothing  ->  fail ("lookupBind: Variable "++show v++" not found.")
         Just (BI xi)  ->  return $ BindVar  $ Vbl xi vc (During n)
         Just (BT xt)  ->  return $ BindTerm $ termTempSync (During n) xt
         Just b -> error $ unlines
                 [ "lookupBind: During was bound to BV"
                 , "v = " ++ show v
                 , "b = " ++ show b
                 , "vbind:\n" ++ show vbind
                 ]

lookupBind (BD (vbind,_,_)) v@(Vbl vi vc vw)
  = case M.lookup (vi,vc) vbind of
     Nothing  ->  fail ("lookupBind: Variable "++show v++" not found.")
     Just (BI xi)  ->  return $ BindVar  $ Vbl xi vc vw
     Just (BT xt)  ->  return $ BindTerm $ termTempSync vw xt
     Just b -> error $ unlines
             [ "lookupBind: Dynamic was bound to BV"
             , "v = " ++ show v
             , "b = " ++ show b
             , "vbind:\n" ++ show vbind
             ]
\end{code}

List variable lookup is very similar:
\begin{code}
lookupLstBind :: Monad m => Binding -> ListVar -> m LstVarBind

lookupLstBind (BD (_,_,lbind)) lv@(LVbl (Vbl i vc Static) is)
  = case M.lookup (i,vc,is) lbind of
     Nothing   ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
     Just bvl  ->  return bvl

lookupLstBind (BD (_,sbind,lbind)) lv@(LVbl (Vbl i vc (During m)) is)
  = case M.lookup m sbind of
     Nothing -> fail ("lookupBind: Subscript ''"++m++"'' not found.")
     Just n ->
       let dn = During n in
       case M.lookup (i,vc,is) lbind of
         Nothing       ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
         Just (BL vl)  ->  return $ BindList  $ map   (gvarTempSync dn) vl
         Just (BS vs)  ->  return $ BindSet   $ S.map (gvarTempSync dn) vs
         Just (BX ts)  ->  return $ BindTerms $ map   (termTempSync dn) ts


lookupLstBind (BD (_,_,lbind)) lv@(LVbl (Vbl i vc vw) is)
  = case M.lookup (i,vc,is) lbind of
     Nothing         ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
     Just (BL vl)  ->  return $ BindList  $ map   (gvarTempSync vw) vl
     Just (BS vs)  ->  return $ BindSet   $ S.map (gvarTempSync vw) vs
     Just (BX ts)  ->  return $ BindTerms $ map   (termTempSync vw) ts
\end{code}

We need to ensure that that the returned variable,
which, if dynamic, is stored in the binding as \texttt{During},
matches the temporality of the variable being looked up.
If the lookup variable is \texttt{Static}, then we leave the result alone.
\textbf{STILL NEED TO TEMPSYNC \texttt{VarList} AND \texttt{VarSet}.}
\begin{code}
varTempSync Static        v             =  v
varTempSync vw@(During m) (Vbl i vc bw@(During n))
 | null n                               =  Vbl i vc vw
 | otherwise                            =  Vbl i vc bw
varTempSync vw            (Vbl i vc _)  =  Vbl i vc vw

lvarTempSync vw (LVbl v is) = LVbl (varTempSync vw v) is

gvarTempSync vw (StdVar v)   =  StdVar (varTempSync vw v)
gvarTempSync vw (LstVar lv)  =  LstVar (lvarTempSync vw lv)

 {- The use of fromJust below will always succeed,
    because none of the smart constructors care about temporality,
    and all we are doing is rebuilding something that got past them
    in the first instance -}
termTempSync vw t@(Var tk v@(Vbl i vc bw))
 | bw == Static                    =  t
 | otherwise                       =  ttsVar tk $ varTempSync vw v
termTempSync vw (Cons tk i ts)     =  Cons tk i $ map (termTempSync vw) ts
termTempSync vw (Bind tk i vs t)   =  fromJust $ bind tk i vs $ termTempSync vw t
termTempSync vw (Lam tk i vl t)    =  fromJust $ lam  tk i vl $ termTempSync vw t
termTempSync vw (Sub tk t s)       =  Sub tk (termTempSync vw t) $ subTempSync vw s
termTempSync vw (Iter tk a p lvs)  =  Iter tk a p $ map (lvarTempSync vw) lvs
termTempSync vw t               =  t

ttsVar tk = getJust "termTempSync var failed." . var tk

subTempSync vw (Substn tsub lsub)
 = fromJust $ substn (map (tsubSync vw) $ S.toList tsub)
                     (map (lsubSync vw) $ S.toList lsub)
 where
      tsubSync vw (v,  t )  =  (v,  termTempSync vw t )
      lsubSync vw (lt, lr)  =  (lt, lvarTempSync vw lr)
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

-- naming concention ct<varname>
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

eadd v1 v2 = Cons tInt n_add [mkV v1, mkV v2]
bradd vw v1 v2 = termTempSync vw $ eadd v1 v2

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
