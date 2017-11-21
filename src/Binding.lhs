\section{Binding}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Binding
( VarBind(..)
, LstVarBind(..)
, Binding
, emptyBinding
, bindVarToVar
, bindVarToTerm
, bindLVarToVList
, bindLVarToVSet
, bindGVarToGVar
, bindGVarToVList
, lookupBind
, lookupLstBind
, int_tst_Binding
) where
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

--import Utilities
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
  \item \texttt{ListVar} to \texttt{VarList} or \texttt{VarSet}.
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
In a scenario where $a$ binds to $b$,
if $a$ is dynamic,
then binding respects temporality
($a \mapsto b, a' \mapsto b', a_m \mapsto b_n, \texttt{a} \mapsto \texttt{b}$).
Also any one of those bindings induces all the others.
\begin{code}
validVarTimeBinding :: VarWhen -> VarWhen -> Bool
validVarTimeBinding Static Textual  =  False
validVarTimeBinding Static _        =  True
validVarTimeBinding pwhen  cwhen    =  pwhen == cwhen
\end{code}

Similar rules apply to list variables.

\newpage
\subsection{Binding Types}

\subsubsection{Binding \texttt{Variable} to \texttt{Variable} or \texttt{Term}}

Given that any binding of a dynamic variable
requires bindings for all of its temporal variants,
we avoid generating four such bindings, by binding from
the variable identifier to a variable that is either \texttt{Static}
or \texttt{During}.
If binding to a term, we add in a \texttt{VarWhen} component
that will serve the same purpose.
The map lookup operation can use this information to re-constitute
the appropriate variable or term.
\begin{code}
data VarBindRange
  = BV Variable
  | BT ( VarWhen -- need to know temporality of pattern variable
       , Term )
  deriving (Eq, Ord, Show, Read)

type VarBinding = M.Map Identifier VarBindRange
\end{code}
We return just the variable or term from a lookup:
\begin{code}
data VarBind
  = BindVar Variable | BindTerm Term deriving Show
\end{code}

\subsubsection{Binding \texttt{ListVar} to \texttt{VarList} or \texttt{VarSet}}

A bit like the binding to terms for variables above,
here we need to track if the temporality of the list variable.
\begin{code}
data LstVarBindRange
 = BL VarWhen VarList
 | BS VarWhen VarSet
 deriving (Eq, Ord, Show, Read)

type ListVarBinding = M.Map ListVar LstVarBindRange
\end{code}
We return just the variable list or set from a lookup:
\begin{code}
data LstVarBind
  = BindList VarList | BindSet VarSet deriving Show
\end{code}

We put these together:
\begin{code}
newtype Binding = BD (VarBinding, ListVarBinding) deriving (Eq, Show, Read)

emptyBinding :: Binding
emptyBinding = BD (M.empty, M.empty)
\end{code}

\newpage
\subsection{Binding Insertion}

If a variable is already present,
then the new binding must be the same,
otherwise we fail.

\subsubsection{Binding Variable to Variable}

\begin{code}
bindVarToVar :: Monad m => Variable -> Variable -> Binding -> m Binding
\end{code}


A \texttt{Static} variable can bind to
any non-\texttt{Textual} thing in the appropriate class.
\begin{code}
bindVarToVar (Vbl v vc Static) cvar@(Vbl x xc xw) binds
 | xw == Textual  =  fail "bindVarToVar: Static cannot bind to Textual"
 | validVarClassBinding vc xc
                  =  insertVV v cvar binds
 | otherwise      =  fail "bindVarToVar: incompatible variable classes"
\end{code}

A \texttt{During} variable can only bind to a \texttt{During} variable in the appropriate class.
One might expect us to be liberal here,
but an attempt by the matcher to do this is an error,
so we catch it here.
\begin{code}
bindVarToVar (Vbl v vc (During _)) cvar@(Vbl x xc (During _)) binds
 | validVarClassBinding vc xc
              =  insertVV v cvar binds
 | otherwise  =  fail "bindVarToVar: incompatible variables"
\end{code}

A dynamic variable can only bind to a dynamic variable of the same
temporality in the appropriate class.
Here we construct a \texttt{During} instance with an empty subscript.
\begin{code}
bindVarToVar (Vbl  v vc vw) (Vbl x xc xw) binds
 | vw /= xw   =  fail "bindVarToVar: different temporalities"
 | validVarClassBinding vc xc
              =  insertVV v (Vbl x xc $ During "") binds
 | otherwise  =  fail "bindVarToVar: incompatible variables"
\end{code}

The insertion function first checks to see if the pattern variable
is already bound.
\begin{code}
insertVV :: Monad m => Identifier -> Variable -> Binding -> m Binding
insertVV i v (BD (vbinds,lbinds))
  = case M.lookup i vbinds of
      Nothing  ->  return $ BD (M.insert i (BV v) vbinds, lbinds)
      Just (BV w) ->
        if compatibleVV v w
        then return $ BD (M.insert i (BV v) vbinds, lbinds)
        else fail "bindVarToVar: variable already bound to different variable."
      _ -> fail "bindVarToVar: variable already bound to term."
\end{code}

A pre-existing binding can only differ from one being added
if they are both \texttt{During}, but the pre-existing one has
an empty subscript, meaning it was induced.
\begin{code}
compatibleVV (Vbl v vc (During _)) (Vbl w wc (During "")) = v == w && vc == wc
compatibleVV v w  = v == w
\end{code}

\newpage
\subsubsection{Binding Variable to Term}

An observation or expression variable can bind to an expression
while a predicate variable can only bind to a predicate.
If we are binding an observation to a term with variant \texttt{Var},
we bind to the underlying variable.
\begin{code}
bindVarToTerm :: Monad m => Variable -> Term -> Binding -> m Binding
bindVarToTerm pv@(ObsVar _ _) ct@(Var _ cv) (BD (vbinds,lbinds))
  | isExpr ct  = return $ BD (M.insert pv (BV cv) vbinds,lbinds)
bindVarToTerm pv@(ObsVar _ _) ct (BD (vbinds,lbinds))
  | isExpr ct  = return $ BD (M.insert pv (BT ct) vbinds,lbinds)
bindVarToTerm pv@(ExprVar _ _) ct (BD (vbinds,lbinds))
  | isExpr ct  = return $ BD (M.insert pv (BT ct) vbinds,lbinds)
bindVarToTerm pv@(PredVar _ _) ct (BD (vbinds,lbinds))
  | isPred ct  = return $ BD (M.insert pv (BT ct) vbinds,lbinds)
bindVarToTerm _ _ _ = fail "bindVarToTerm: invalid var. -> term binding."
\end{code}

\subsubsection{Binding List-Variables to Variable-Lists}

An observation list-variable can bind to a list that is
a mix of observation and expression general variables.
\begin{code}
isObsOrExpr gv = isObsGVar gv || isExprGVar gv
\end{code}
Expression/Predicate list-variables can only bind to lists
of the same class of general variable.
\begin{code}
bindLVarToVList :: Monad m => ListVar -> VarList -> Binding -> m Binding
bindLVarToVList lv vl (BD (vbinds,lbinds))
 | isObsLVar lv && all isObsOrExpr vl
                               = return $ BD (vbinds,M.insert lv (BL vl) lbinds)
 | isExprLVar lv && all isExprGVar vl
                               = return $ BD (vbinds,M.insert lv (BL vl) lbinds)
 | isPredLVar lv && all isPredGVar vl
                               = return $ BD (vbinds,M.insert lv (BL vl) lbinds)
bindLVarToVList _ _ _ = fail "bindLVarToVList: invalid lvar. -> vlist binding."
\end{code}

\subsubsection{Binding List-Variables to Variable-Sets}

An observation list-variable can bind to a set that is
a mix of observation and expression general variables.
Expression/Predicate list-variables can only bind to sets
of the same class of general variable.
\begin{code}
bindLVarToVSet :: Monad m => ListVar -> VarSet -> Binding -> m Binding
bindLVarToVSet lv vs (BD (vbinds,lbinds))
 | isObsLVar lv && all isObsOrExpr vl
                               = return $ BD (vbinds,M.insert lv (BS vs) lbinds)
 | isExprLVar lv && all isExprGVar vl
                               = return $ BD (vbinds,M.insert lv (BS vs) lbinds)
 | isPredLVar lv && all isPredGVar vl
                               = return $ BD (vbinds,M.insert lv (BS vs) lbinds)
 where vl = S.toList vs
bindLVarToVSet _ _ _ = fail "bindLVarToVSet: invalid lvar. -> vset binding."
\end{code}

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

\newpage
\subsection{Binding Lookup}

Binding lookup is very straightforward,
with the minor wrinkle that we want to do it
in a general monadic setting.
\begin{code}
lookupBind :: Monad m => Binding -> Variable -> m VarBindRange
lookupBind (BD (vbinds,_)) v
  = case M.lookup v vbinds of
      Nothing   ->  fail ("lookupBind: Variable "++show v++" not found.")
      Just vbr  ->  return vbr

lookupLstBind :: Monad m => Binding -> ListVar -> m LstVarBindRange
lookupLstBind (BD (_,lbinds)) lv
  = case M.lookup lv lbinds of
      Nothing    ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
      Just lvbr  ->  return lvbr
\end{code}


\newpage
\subsection{Binding Internal Tests}

\begin{code}
int_tst_Binding :: [TF.Test]
int_tst_Binding
 = [tst_bind_VarToVar]


tst_bind_VarToVar :: TF.Test

-- naming concention ct<varname>
-- c = o (ObsV), e (ExprV), p (PredV)
-- t = s (Static), b (Before), d (During), a (After), t (Textual)

osg = ObsVar (fromJust $ ident "g") Static
osin = ObsVar (fromJust $ ident "in") Static
osout = ObsVar (fromJust $ ident "out") Static

v = fromJust $ ident "v"
obv = ObsVar v Before ; oav = ObsVar v After ; otv = ObsVar v Textual
odv = ObsVar v (During "") ; odvm = ObsVar v (During "m")
x = fromJust $ ident "x"
obx = ObsVar x Before  ; oax = ObsVar x After ; otx = ObsVar x Textual
odx = ObsVar x (During "") ; odxm = ObsVar x (During "m")

tst_bind_VarToVar
 = testGroup "bind Var to Var"
    [ testCase "Obs-Static g |-> in -- should succeed"
        ( bindVarToVar osg osin emptyBinding
          @?= Just (BD (M.fromList [(osg,BV osin)], M.empty)) )
    , testCase "Obs-Before v |-> x -- should succeed, with dynamic inducing"
        ( bindVarToVar obv obx emptyBinding
          @?= Just (BD (M.fromList [ (obv,BV obx), (odv,BV odx)
                                   , (oav,BV oax), (otv,BV otx)
                                   ], M.empty)) )
    , testCase "Static conflict  g,g |-> in,out -- should fail"
        ( ( bindVarToVar osg osin $
                         fromJust $ bindVarToVar osg osout $ emptyBinding )
           @?= Nothing )
    ]

tstBVV = defaultMain [tst_bind_VarToVar]
\end{code}
