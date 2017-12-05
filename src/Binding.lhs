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
import Data.List (nub)
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

We can sum the rules as follows

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
                  =  insertVV v Static cvar binds
 | otherwise      =  fail "bindVarToVar: incompatible variable classes"
\end{code}

A \texttt{During} variable can only bind to a \texttt{During} variable
in the appropriate class.
\begin{code}
bindVarToVar (Vbl v vc vw@(During _)) cvar@(Vbl x xc (During _)) binds
 | validVarClassBinding vc xc
              =  insertVV v vw cvar binds
 | otherwise  =  fail "bindVarToVar: incompatible variables"
\end{code}

A dynamic variable can only bind to a dynamic variable of the same
temporality in the appropriate class.
Regardless of the actual temporality,
we construct a \texttt{During} instance with an empty subscript if new,
or a pre-existing subscript if not.
\begin{code}
bindVarToVar (Vbl  v vc vw) (Vbl x xc xw) binds
 | vw /= xw   =  fail "bindVarToVar: different temporalities"
 | validVarClassBinding vc xc
              =  insertVV v newDuring (Vbl x xc $ newDuring) binds
 | otherwise  =  fail "bindVarToVar: incompatible variables"
\end{code}

We have a ``new''\texttt{During} value:
\begin{code}
newDuring = During ""
\end{code}

\newpage
The insertion function first checks to see if the pattern variable
is already bound.
We expect the following behaviour,
where $s$ is \texttt{Static}, $\texttt{v}$ and $\texttt{x}$ are \texttt{Textual},
and $v$ and $x$ with or without decoration, are any other \texttt{Dynamic},
and $i_s$ and $i_v$ are the respective identifiers  underlying $s$ and the $v$s:

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
  \underline{prior bind} &&&
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

The following code expects:
 the \texttt{VarWhen} argument to be \texttt{Static} or \texttt{During};
  and the \texttt{Variable} argument
to have \texttt{During} temporality
if the \texttt{VarWhen} parameter is \texttt{During}.
\begin{code}
insertVV :: Monad m => Identifier -> VarWhen -> Variable -> Binding -> m Binding

insertVV i Static x binds@(BD (vbinds,lbinds))
  = case M.lookup i vbinds of
      Nothing  ->  return $ BD (M.insert i (BV x) vbinds, lbinds)
      Just (BV w)
       | w == x  ->  return binds
       | otherwise -> fail "bindVarToVar: static-var. bound to other variable."
      _ -> fail "bindVarToVar: static-var. already bound to term."

insertVV i vw@(During m) x@(Vbl xi xc (During n)) binds@(BD (vbinds,lbinds))
  = case M.lookup i vbinds of
      Nothing  ->  return $ BD (M.insert i (BV x) vbinds, lbinds)
      Just (BV w@(Vbl bi bc (During p)))
        | bi /= xi ||  bc /= xc
            ->  fail "bindVarToVar: variable bound to other variable."
        | null p  ->  return $ BD (M.insert i (BV x) vbinds, lbinds)
        | p == n  ->  return binds
        | otherwise
            ->  fail "bindVarToVar: variable bound to other subscript."
      _  ->  fail "bindVarToVar: variable already bound to term."

insertVV i vw x _
  = error $ unlines
      [ "bindVarToVar: unexpected argument combination"
      , "i  =  " ++ show i
      , "vw =  " ++ show vw
      , "x  =  " ++ show x
       ]
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

For list-variable binding we require all variables in the list
to have a class compatible with the list variable,
and to have the same temporality.
The exception is if the list-variable is static,
in which case we need to ensure that there are no textual variables present.
\begin{code}
validStaticGVarClass vc gvar
  = gvarWhen gvar /= Textual && validVarClassBinding vc (gvarClass gvar)

vlCompatible vc Static vl  =  all (validStaticGVarClass vc) vl
vlCompatible vc vw vl      =  vlComp vc vw S.empty vl

vlComp _ _ vws []  =  S.size vws <= 1
vlComp vc vw vws (gv:gvs)
 | gvw == Static                           =  False
 | validVarClassBinding vc (gvarClass gv)  =  vlComp vc vw vws' gvs
 | otherwise                               =  False
 where
   gvw = gvarWhen gv
   vws' = S.insert gvw vws

-- don't force Static
forceVNullDuring v@(Vbl _ _  Static)  =  v
forceVNullDuring   (Vbl i vc _     )  =  Vbl i vc (During "")

forceLNullDuring (LVbl v is)  =  LVbl (forceVNullDuring v) is

forceGNullDuring (StdVar v)   =  StdVar $ forceVNullDuring v
forceGNullDuring (LstVar lv)  =  LstVar $ forceLNullDuring lv
\end{code}

\begin{code}
bindLVarToVList :: Monad m => ListVar -> VarList -> Binding -> m Binding
\end{code}

A Static list-variable binds to any list without \texttt{Textual} variables.
\begin{code}
bindLVarToVList lv@(LVbl (Vbl i vc Static) is) vl binds
 | vlCompatible vc Static vl  =  insertLL i is Static vl binds
\end{code}

If our pattern list-variable has temporality \texttt{During},
then we pass the the candidate variable list in unchanged.
Otherwise,
we map all \texttt{VarWhen} in the variable list to \texttt{During ""}.
\begin{code}
bindLVarToVList lv@(LVbl (Vbl i vc vw@(During _)) is) vl binds
 | vlCompatible vc vw vl  =  insertLL i is vw vl binds
bindLVarToVList lv@(LVbl (Vbl i vc vw) is) vl binds
 | vlCompatible vc vw vl'  =  insertLL i is vw vl' binds
 where vl' = map forceGNullDuring vl
\end{code}

Anything else fails.
\begin{code}
bindLVarToVList _ _ _ = fail "bindLVarToVList: invalid lvar. -> vlist binding."
\end{code}

\begin{code}
insertLL :: Monad m => Identifier -> [Identifier] -> VarWhen -> VarList
         -> Binding -> m Binding
insertLL i is vw vl (BD (vbinds,lbinds))
 = return $ BD (vbinds, M.insert (i,is) (BL vw vl) lbinds)
\end{code}

\newpage
\subsubsection{Binding List-Variables to Variable-Sets}

Similar code to \texttt{bindLVarToVList} above, except we have sets.
\begin{code}
vsCompatible vc Static vs  =  all (validStaticGVarClass vc) vs
vsCompatible vc vw vs      =  vlComp vc vw S.empty (S.toList vs)
\end{code}

\begin{code}
bindLVarToVSet :: Monad m => ListVar -> VarSet -> Binding -> m Binding

bindLVarToVSet lv@(LVbl (Vbl i vc Static) is) vs binds
 | vsCompatible vc Static vs  =  insertLS i is Static vs binds

bindLVarToVSet lv@(LVbl (Vbl i vc vw@(During _)) is) vs binds
 | vsCompatible vc vw vs  =  insertLS i is vw vs binds
bindLVarToVSet lv@(LVbl (Vbl i vc vw) is) vs binds
 | vsCompatible vc vw vs'  =  insertLS i is vw vs' binds
 where vs' = S.map forceGNullDuring vs

bindLVarToVSet _ _ _ = fail "bindLVarToVSet: invalid lvar. -> vset binding."
\end{code}

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
lookupBind (BD (vbinds,_)) (Vbl i _ vw)
  = case M.lookup i vbinds of
      Nothing        ->  fail ("lookupBind: Variable "++show v++" not found.")
      Just (BV v)    ->  return $ BindVar  $ varTempSync  vw v
      Just (BT _ t)  ->  return $ BindTerm $ termTempSync vw t

lookupLstBind :: Monad m => Binding -> ListVar -> m LstVarBind
lookupLstBind (BD (_,lbinds)) lv@(LVbl (Vbl i _ vw) is)
  = case M.lookup (i,is) lbinds of
     Nothing         ->  fail ("lookupLstBind: ListVar "++show lv++"not found.")
     Just (BL _ vl)  ->  return $ BindList $ map   (gvarTempSync vw) vl
     Just (BS _ vs)  ->  return $ BindSet  $ S.map (gvarTempSync vw) vs
\end{code}

We need to ensure that that the returned variable,
which, if dynamic,  is stored in the binding as \texttt{During},
matches the temporality of the variable being looked up.
If the lookup variable is \texttt{Static}, then we eave the result alone.
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
 | bw == Static                 =  t
 | otherwise                    =  fromJust $ var tk $ varTempSync vw v
termTempSync vw (Cons tk i ts)     =  Cons tk i $ map (termTempSync vw) ts
termTempSync vw (Bind tk i vs t)   =  fromJust $ bind tk i vs $ termTempSync vw t
termTempSync vw (Lam tk i vl t)    =  fromJust $ lam  tk i vl $ termTempSync vw t
termTempSync vw (Sub tk t s)       =  Sub tk (termTempSync vw t) $ subTempSync vw s
termTempSync vw (Iter tk a p lvs)  =  Iter tk a p $ map (lvarTempSync vw) lvs
termTempSync vw t               =  t

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
    , testCase "Obs-During v_m |-> x_m -- should succeed, with dynamic inducing"
        ( bindVarToVar odvm odxm emptyBinding
          @?= Just (BD (M.fromList [(v,BV odxm)], M.empty)) )
    , testCase "Obs-During v_m |-> x_n -- should succeed"
        ( bindVarToVar odvm odxn emptyBinding
          @?= Just (BD (M.fromList [(v,BV odxn)], M.empty)) )
    , testCase "Obs-Before-During v ; v_m |-> x ; x_n -- should succeed"
        ( ( bindVarToVar odvm odxn $ fromJust
          $ bindVarToVar obv obx emptyBinding )
          @?= Just (BD (M.fromList [(v,BV odxn)], M.empty)) )
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
