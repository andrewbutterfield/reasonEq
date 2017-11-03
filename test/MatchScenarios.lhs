\section{Match Scenarios}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module MatchScenarios ( tst_match_scenarios ) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub, sort)

import Test.HUnit
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import LexBase
import AST
import VarData
import Binding
import Matching
\end{code}

\newpage
\subsection{Matching Scenario Introduction}

We create high-level matching scenarios to test the
fitness for purpose of the matching algorithms.
We place particular emphasis on UTP-specific matching requirements.

Here is our initial set of scenarios:
\begin{description}
  \item [Reserved List-Variables] $O$, $M$, and $S$.
  \item[($O$,$S$,$M$)-matching]
    Matching: $\exists ok_m,S_m \bullet \ldots$
    \\against: $\exists O_n \bullet \ldots$
    \\ yields: $O_n \mapsto \setof{ok_m} \cup S_m$.
  \item[Sequential Composition]
   $$
    P ; Q
    ~\defs~
    \exists O_m \bullet P[O_m/O'] \land Q[O_m/O]
   $$
  \item[Assignment]
    $$
      x := e
      ~\defs~
      ok \implies ok' \land x' = e \land S'\less x = S\less x
    $$
  \item[Simultaneous Assignment]
    \begin{eqnarray*}
      \lefteqn{x_1,\ldots,x_n ::= e_1, \ldots , e_n}
    \\ &=& \lst x ::= \lst e
    \\ &\defs&
         ok \implies ok'
         \land x'_1 = e_1 \land \ldots \land x'_n = e_n
         \land S'\less{x_1,\ldots,x_n} = S\less{x_1,\ldots,x_n}
    \\ &=& ok \implies ok'
        \land \lst x' = \lst e
        \land S'\less{\lst x} = S\less{\lst x}
    \end{eqnarray*}
\end{description}
\subsection{Predefined Types}

We assume the existence of types
for boolean ($\Bool$)
and integer ($\Int$) values.
\begin{code}
bool = GivenType $ fromJust $ ident "B"
int  = GivenType $ fromJust $ ident "Z"
\end{code}

\newpage
\subsection{Reserved List-Variables}

We shall assume an imperative language with three program variables,
$x$, $y$, and $z$, and model observations $ok$ and $ok'$.

We have the following ``known'' variables:

Model observations regarding termination.
\begin{eqnarray*}
   ok, ok'         &:&   \Bool
\end{eqnarray*}
\begin{code}
ok  = PreVar  $ fromJust $ ident "ok" ; okVMR  = KnownVar bool
ok' = PostVar $ fromJust $ ident "ok" ; ok'VMR = KnownVar bool
\end{code}

Script observations regarding values of program variables.
\begin{eqnarray*}
   x,x',y,y',z,z'  &:&   \Int
\end{eqnarray*}
\begin{code}
x = PreVar  $ fromJust $ ident "x"  ;  x' = PostVar $ fromJust $ ident "x"
y = PreVar  $ fromJust $ ident "y"  ;  y' = PostVar $ fromJust $ ident "y"
z = PreVar  $ fromJust $ ident "z"  ;  z' = PostVar $ fromJust $ ident "z"
\end{code}

List-variables that classify observations.
\begin{eqnarray*}
   S             &\defs& \setof{x,y,z}
\\ S'            &\defs& \setof{x',y',z'}
\\ M             &\defs& \setof{ok}
\\ M'            &\defs& \setof{ok'}
\\ O             &\defs& M \cup S
\\ O'            &\defs& M'\cup S'
\end{eqnarray*}
\begin{code}
lS = PreVars  $ fromJust $ ident "S"  ;  lS' = PostVars $ fromJust $ ident "S"
lM = PreVars  $ fromJust $ ident "M"  ;  lM' = PostVars $ fromJust $ ident "M"
lO = PreVars  $ fromJust $ ident "O"  ;  lO' = PostVars $ fromJust $ ident "O"
\end{code}

Wrap it all up in a ``Design'' variable-table.
We have two variants,
one which defines $O$, $S$ and $M$ in terms of listsm
the other doing it in terms of sets.
\begin{code}
kvDesign =
    akv ok bool $ akv ok' bool
  $ akv x int $ akv x' int $ akv y int $ akv y' int $ akv z int $ akv z' int
  $ newVarTable

vtL_Design =
    aklv lS (vwrap [x,y,z]) $ aklv lS' (vwrap [x',y',z'])
  $ aklv lM (vwrap [ok])    $ aklv lM' (vwrap [ok'])
  $ aklv lO (lwrap [lM,lS]) $ aklv lO' (lwrap [lM',lS'])
  $ kvDesign

vtS_Design =
    aksv lS (vswrap [x,y,z]) $ aksv lS' (vswrap [x',y',z'])
  $ aksv lM (vswrap [ok])    $ aksv lM' (vswrap [ok'])
  $ aksv lO (lswrap [lM,lS]) $ aksv lO' (lswrap [lM',lS'])
  $ kvDesign

vwrap = map StdVar ;  vswrap = S.fromList . vwrap
lwrap = map LstVar ;  lswrap = S.fromList . lwrap
akv v t tbl = fromJust $ addKnownVar v t tbl
aklv lv vl tbl = fromJust $ addKnownVarList lv vl tbl
aksv lv vs tbl = fromJust $ addKnownVarSet lv vs tbl
\end{code}

Tests:
\begin{code}
tst_reserved_listvars
 = [ testGroup "Reserved List Variables"
     [ testCase "|-  x,y :: S  -- succeeds."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y])
            (lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y]) emptyBinding :: [Binding]) )
     , testCase "|-  x,y,z :: S  -- doesn't match, exceeding heuristic limit."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "L_Design |-  x,y,z :: S  -- matches."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ))
     , testCase "S_Design |-  x,y,z :: S  -- fails."
       ( vlMatch [vtS_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "S_Design |-  {x,y,z} :: {S}  -- matches at least once."
       ( vsMatch [vtS_Design] emptyBinding S.empty S.empty
            (vswrap [x,y,z])
            (lswrap [lS])
         @?= ( bindLVarToVSet lS (vswrap [x,y,z]) emptyBinding :: [Binding] ))
     , testCase "L_Design |-  {x,y,z} :: {S}  -- fails."
       ( vsMatch [vtL_Design] emptyBinding S.empty S.empty
            (vswrap [x,y,z])
            (lswrap [lS])
         @?= Nothing )
     , testCase "x,y,z,S @ L_Design  |-  x,y,z :: S  -- matches."
       ( vlMatch [vtL_Design] emptyBinding
            (S.fromList $ vwrap [x,y,z])
            (S.fromList $ lwrap [lS])
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ) )
     , testCase "L_Design  |-  x',y',z' :: S  -- shouldn't match."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x',y',z'])
            (lwrap [lS])
         @?= Nothing )
     , testCase "L_Design  |-  x,y',z :: S  -- shouldn't match."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x,y',z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "L_Design  |-  x,y,z :: S'  -- shouldn't match."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS'])
         @?= Nothing )
     , testCase "L_Design  |-  x',y',z' :: S'  -- matches."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x',y',z'])
            (lwrap [lS'])
         @?=
         ( bindLVarToVList lS' (vwrap [x',y',z']) emptyBinding :: [Binding] ) )
     , testCase "L_Design  |-  M,S :: O  -- matches."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (lwrap [lM,lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (lwrap [lM,lS]) emptyBinding :: [Binding] ) )
     , testCase "L_Design  |-  S,M :: O  -- fails due to ordering."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (lwrap [lS,lM])
            (lwrap [lO])
         @?= Nothing )
     , testCase "|-  M,S :: O  -- matches ."
       ( vlMatch [] emptyBinding S.empty S.empty
            (lwrap [lM,lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (lwrap [lM,lS]) emptyBinding :: [Binding] ) )
     , testCase "L_Design |-  ok,x,y,z :: M,S  -- matches."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [ok,x,y,z])
            (lwrap [lM,lS])
         @?=
         (  (bindLVarToVList lM (vwrap [ok]) $ fromJust $
            bindLVarToVList lS (vwrap [x,y,z]) emptyBinding) :: Maybe Binding ) )
     , testCase "L_Design |-  ok,x,y,z :: S,M  -- shouldn't match."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [ok,x,y,z])
            (lwrap [lS,lM])
         @?= Nothing )
     , testCase "L_Design |-  x,y,z,ok :: M,S  -- shouldn't match."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z,ok])
            (lwrap [lM,lS])
         @?= Nothing )
     , testCase "L_Design  |-  ok,S :: O  -- matches."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [ok] ++ lwrap [lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [ok] ++lwrap [lS]) emptyBinding
           :: [Binding] ) )
     , testCase "L_Design  |-  S,ok :: O  -- fails due to ordering."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (lwrap [lS] ++ vwrap [ok])
            (lwrap [lO])
         @?= Nothing )
     , testCase "L_Design  |-  ok :: M,S  -- shouldn't match."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [ok] )
            (lwrap [lM,lS])
         @?= Nothing )
     , testCase "|-  x,y :: O  -- matches."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [x,y]) emptyBinding :: [Binding] ) )
     , testCase "|-  x,y' :: O  -- matches."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y'])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [x,y']) emptyBinding :: [Binding] ) )
     , testCase "|-  e,x :: O  -- matches ."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [e,x])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [e,x]) emptyBinding :: [Binding] ) )
     ]
   ]

e = PreExpr $ fromJust $ ident "e"
\end{code}

\newpage
\subsection{Exported Tests}
\begin{code}
tst_match_scenarios :: [TF.Test]

tst_match_scenarios
  = [ testGroup "\nMatching Scenarios"
       tst_reserved_listvars
    ]
\end{code}
