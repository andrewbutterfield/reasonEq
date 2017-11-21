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
  | BT VarWhen Term -- need to know temporality of pattern variable.
  deriving (Eq, Ord, Show, Read)

type VarBinding = M.Map Identifier VarBindRange
\end{code}
We return just the variable or term from a lookup:
\begin{code}
data VarBind
  = BindVar Variable | BindTerm Term deriving (Eq, Show)
\end{code}

\subsubsection{Binding \texttt{ListVar} to \texttt{VarList} or \texttt{VarSet}}

We bibd to either a list or set of variables,
and record the temporality (\texttt{Static} or \texttt{During}).
We use the variable identifier and the list of `subtracted` identifiers
as the map key.
\begin{code}
data LstVarBindRange
 = BL VarWhen VarList
 | BS VarWhen VarSet
 deriving (Eq, Ord, Show, Read)

type ListVarBinding = M.Map (Identifier,[Identifier]) LstVarBindRange
\end{code}
We return just the variable list or set from a lookup:
\begin{code}
data LstVarBind = BindList VarList | BindSet VarSet deriving (Eq, Show)
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
compatibleVV :: Variable -> Variable -> Bool
compatibleVV (Vbl v vc (During _)) (Vbl w wc (During ""))  =  v == w && vc == wc
compatibleVV newvar                oldvar                  =  newvar == oldvar
\end{code}

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
bindVarToTerm pv@(Vbl v vc Static) ct binds
 | validVarTermBinding vc (termkind ct) = insertVT v Static ct binds
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
\begin{code}
bindVarToTerm pv@(Vbl v ExprV vt) ct binds
 | isPred ct  =  fail "bindVarToTerm: expr. variable cannot bind to predicate."
 | vt `isTemporalityOf` ct  =  insertVT v vt ct binds
 | otherwise  = fail "bindVarToTerm: expr.-var. to mixed temporality"
\end{code}
Dynamic predicate variables can only bind to
predicate terms, all of whose dynamic variables have the same temporality.
\begin{code}
bindVarToTerm pv@(Vbl v PredV vt) ct binds
 | isExpr ct  =  fail "bindVarToTerm: pred. variable cannot bind to expression."
 | vt `isTemporalityOf` ct  =  insertVT v vt ct binds
 | otherwise  = fail "bindVarToTerm: pred.-var. to mixed temporality"
\end{code}

Catch-all
\begin{code}
bindVarToTerm pv ct _
 = error $ unlines
     [ "bindVarToTerm: fell off end"
     , "pv = " ++ show pv
     , "ct = " ++ show ct ]
\end{code}

The insertion function cannot check to see if all dynamic variables
in the term have the same temporality as the variable.
This has to be done by the matcher, as it only needs to hold
for ``known'' observation variables.

First, it checks if the pattern variable
is already bound.
\begin{code}
insertVT :: Monad m => Identifier -> VarWhen -> Term -> Binding -> m Binding
insertVT i vw t (BD (vbinds,lbinds))
  = case M.lookup i vbinds of
      Nothing  ->  return $ BD (M.insert i (BT vw t) vbinds, lbinds)
      Just (BT ww s) ->
        if vw == ww && compatibleTT t s
        then return $ BD (M.insert i (BT vw t) vbinds, lbinds)
        else fail "bindVarToTerm: variable already bound to different variable."
      _ -> fail "bindVarToTerm: variable already bound to variable."
\end{code}

Checking all dynamic variables in a term have the specified temporality:
\begin{code}
isTemporalityOf :: VarWhen -> Term -> Bool

(During _) `isTemporalityOf` (Var _ (Vbl _ _ (During _)))  =  True
dt `isTemporalityOf` (Var _ (Vbl _ _ vdt))                 =  dt == vdt

dt `isTemporalityOf` (Cons _ _ ts)   =  all (isTemporalityOf dt) ts
dt `isTemporalityOf` (Bind _ _ _ t)  =  dt `isTemporalityOf` t
dt `isTemporalityOf` (Lam _ _ _ t)   =  dt `isTemporalityOf` t
dt `isTemporalityOf` (Sub _ t sub)   =  all (isTemporalityOf dt) (t:termsof sub)
 where termsof (Substn tsub _)       =  map snd $ S.toList tsub
dt `isTemporalityOf` _               =  True
\end{code}

\newpage
A pre-existing bound term can only differ from one being added
if they both contain just\texttt{During} dynamic variables,
and those in the pre-existing term have empty subscripts.
In effect we have an equality check with one weakening,
so that new \verb'(During \_)' is fine against old \verb'(During "")'.
\begin{code}
compatibleTT :: Term -> Term -> Bool

compatibleTT (Var nk (Vbl ni nc (During _))) (Var ok (Vbl oi oc (During "")))
  =  ni == oi && nc == oc && nk == ok

compatibleTT (Cons nk ni nts) (Cons ok oi ots)
  =  ni == oi && nk == ok && compTTs nts ots
compatibleTT (Bind nk ni nvs nt) (Bind ok oi ovs ot)
  =  ni == oi && nk == ok && nvs == ovs && compatibleTT nt ot
compatibleTT (Lam nk ni nvl nt) (Lam ok oi ovl ot)
  =  ni == oi && nk == ok && nvl == ovl && compatibleTT nt ot
compatibleTT (Sub nk nt ns) (Sub ok ot os)
  =  nk == ok && compatibleTT nt ot && compSS ns os
compatibleTT (Iter nk ni np nlvs) (Iter ok oi op olvs)
  =  np == op && ni == oi && nk == ok && nlvs == olvs

compatibleTT t s  =  t == s

compTTs :: [Term] -> [Term] -> Bool
compTTs [] [] = True
compTTs (_:_) [] = False
compTTs [] (_:_) = False
compTTs (nt:nts) (ot:ots) = compatibleTT nt ot && compTTs nts ots

compSS :: Substn -> Substn -> Bool
compSS (Substn ntsub nlvsub) (Substn otsub olvsub)
  = nlvsub == olvsub && compTSTS ntsub otsub

compTSTS :: TermSub -> TermSub -> Bool
compTSTS ntsub otsub
 = nvs == ovs && compTTs nts ots
 where
   (nvs,nts) = unzip $ S.toList ntsub
   (ovs,ots) = unzip $ S.toList otsub
\end{code}

\newpage
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
bindLVarToVList lv@(LVbl (Vbl i _ vw) is) vl binds
 | isObsLVar lv && all isObsOrExpr vl  =  insertLL i is vw vl binds
 | isExprLVar lv && all isExprGVar vl  =  insertLL i is vw vl binds
 | isPredLVar lv && all isPredGVar vl  =  insertLL i is vw vl binds
bindLVarToVList _ _ _ = fail "bindLVarToVList: invalid lvar. -> vlist binding."
\end{code}

\textbf{We need \texttt{insertLL} to check for pre-existing entries
and compatibility !!!}
\begin{code}
insertLL :: Monad m => Identifier -> [Identifier] -> VarWhen -> VarList
         -> Binding -> m Binding
insertLL i is vw vl (BD (vbinds,lbinds))
 = return $ BD (vbinds, M.insert (i,is) (BL vw vl) lbinds)
\end{code}

\subsubsection{Binding List-Variables to Variable-Sets}

An observation list-variable can bind to a set that is
a mix of observation and expression general variables.
Expression/Predicate list-variables can only bind to sets
of the same class of general variable.
\begin{code}
bindLVarToVSet :: Monad m => ListVar -> VarSet -> Binding -> m Binding
bindLVarToVSet lv@(LVbl (Vbl i _ vw) is) vs binds
 | isObsLVar lv && all isObsOrExpr vs  =  insertLS i is vw vs binds
 | isExprLVar lv && all isExprGVar vs  =  insertLS i is vw vs binds
 | isPredLVar lv && all isPredGVar vs  =  insertLS i is vw vs binds
bindLVarToVSet _ _ _ = fail "bindLVarToVSet: invalid lvar. -> vset binding."
\end{code}

\textbf{We need \texttt{insertLL} to check for pre-existing entries
and compatibility !!!}
\begin{code}
insertLS :: Monad m => Identifier -> [Identifier] -> VarWhen -> VarSet
         -> Binding -> m Binding
insertLS i is vw vs (BD (vbinds,lbinds))
 = return $ BD (vbinds, M.insert (i,is) (BS vw vs) lbinds)
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
with the minor wrinkle that we need to ensure that
any found \texttt{During} subscripts are modified to be the
same as that of the variable being looked up
(it will be a \texttt{During} variable itself in that case).
\begin{code}
lookupBind :: Monad m => Binding -> Variable -> m VarBind
lookupBind (BD (vbinds,_)) (Vbl i _ _)
  = case M.lookup i vbinds of
      Nothing        ->  fail ("lookupBind: Variable "++show v++" not found.")
      Just (BV v)    ->  return $ BindVar  v -- sync temporality !
      Just (BT _ t)  ->  return $ BindTerm t -- sync temporality !

lookupLstBind :: Monad m => Binding -> ListVar -> m LstVarBind
lookupLstBind (BD (_,lbinds)) lv@(LVbl (Vbl i _ _) is)
  = case M.lookup (i,is) lbinds of
     Nothing         ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
     Just (BL _ vl)  ->  return $ BindList vl -- sync temporality !
     Just (BS _ vs)  ->  return $ BindSet  vs -- sync temporality !
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

g = fromJust $ ident "g"
osg = ObsVar (fromJust $ ident "g") Static
osin = ObsVar (fromJust $ ident "in") Static
osout = ObsVar (fromJust $ ident "out") Static

v = fromJust $ ident "v"
obv = ObsVar v Before ; oav = ObsVar v After ; otv = ObsVar v Textual
odv = ObsVar v (During "") ; odvm = ObsVar v (During "m")
x = fromJust $ ident "x"
obx = ObsVar x Before  ; oax = ObsVar x After ; otx = ObsVar x Textual
odx = ObsVar x (During "")
odxm = ObsVar x (During "m") ; odxn = ObsVar x (During "n")

tst_bind_VarToVar
 = testGroup "bind Var to Var"
    [ testCase "Obs-Static g |-> in -- should succeed"
        ( bindVarToVar osg osin emptyBinding
          @?= Just (BD (M.fromList [(g,BV osin)], M.empty)) )
    , testCase "Obs-Before v |-> x -- should succeed, with dynamic inducing"
        ( bindVarToVar obv obx emptyBinding
          @?= Just (BD (M.fromList [(v,BV odx)], M.empty)) )
    , testCase "Obs-Before v_m |-> x_m -- should succeed, with dynamic inducing"
        ( bindVarToVar obv obx emptyBinding
          @?= Just (BD (M.fromList [(v,BV odxm)], M.empty)) )
    , testCase "Obs-Before v_m |-> x_n -- should succeed, with dynamic inducing"
        ( bindVarToVar obv obx emptyBinding
          @?= Just (BD (M.fromList [(v,BV odxn)], M.empty)) )
    , testCase "Static conflict  g,g |-> in,out -- should fail"
        ( ( bindVarToVar osg osin $
                         fromJust $ bindVarToVar osg osout $ emptyBinding )
           @?= Nothing )
    ]

tstBVV = defaultMain [tst_bind_VarToVar]
\end{code}
