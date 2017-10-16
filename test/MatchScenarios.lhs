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
import Test.Framework as TF (testGroup, Test)
--import Test.Framework as TF (defaultMain, testGroup, Test)
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
\\ O             &\defs& S \cup M
\\ O'            &\defs& S'\cup M'
\end{eqnarray*}
\begin{code}
lS = PreVars  $ fromJust $ ident "S"  ;  lS' = PostVars $ fromJust $ ident "S"
lM = PreVars  $ fromJust $ ident "M"  ;  lM' = PostVars $ fromJust $ ident "M"
lO = PreVars  $ fromJust $ ident "O"  ;  lO' = PostVars $ fromJust $ ident "O"
\end{code}

Wrap it all up in a ``Design'' variable-table:
\begin{code}
vtDesign =
    akv ok bool $ akv ok' bool
  $ akv x int $ akv x' int $ akv y int $ akv y' int $ akv z int $ akv z' int
  $ aklv lS (vwrap [x,y,z]) $ aklv lS' (vwrap [x',y',z'])
  $ aklv lM (vwrap [ok])    $ aklv lM' (vwrap [ok'])
  $ aklv lO (lwrap [lS,lM]) $ aklv lO' (lwrap [lS',lM'])
  $ newVarTable

vwrap = map StdVar ;  vswrap = sort . vwrap
lwrap = map LstVar ;  lswrap = sort . lwrap
akv v t tbl = fromJust $ addKnownVar v t tbl
aklv lv vl tbl = fromJust $ addKnownListVar lv vl tbl
\end{code}

Tests:
\begin{code}
tst_reserved_listvars
 = [ testGroup "Reserved List Variables"
     [ testCase "|-  x,y,z :: S  -- shouldn't match."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "Design |-  x,y,z :: S  -- matches at least once."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ))
     , testCase "x,y,z,S @ Design  |-  x,y,z :: S  -- matches at least once."
       ( vlMatch [vtDesign] emptyBinding
            (S.fromList $ vwrap [x,y,z])
            (S.fromList $ lwrap [lS])
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ) )
     , testCase "Design  |-  x',y',z' :: S  -- shouldn't match."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x',y',z'])
            (lwrap [lS])
         @?= Nothing )
     , testCase "Design  |-  x,y',z :: S  -- shouldn't match."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x,y',z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "Design  |-  x,y,z :: S'  -- shouldn't match."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS'])
         @?= Nothing )
     , testCase "Design  |-  x',y',z' :: S'  -- matches at least once."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x',y',z'])
            (lwrap [lS'])
         @?=
         ( bindLVarToVList lS' (vwrap [x',y',z']) emptyBinding :: [Binding] ) )
     , testCase "Design  |-  M,S :: O  -- matches at least once."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (lwrap [lM,lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (lwrap [lM,lS]) emptyBinding :: [Binding] ) )
     , testCase "|-  M,S :: O  -- matches at least once."
       ( vlMatch [] emptyBinding S.empty S.empty
            (lwrap [lM,lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (lwrap [lM,lS]) emptyBinding :: [Binding] ) )
     , testCase "Design |-  ok,x,y,z :: M,S  -- matches at least once."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [ok,x,y,z])
            (lwrap [lM,lS])
         @?=
         (  (bindLVarToVList lM (vwrap [ok]) $ fromJust $
            bindLVarToVList lS (vwrap [x,y,z]) emptyBinding) :: Maybe Binding ) )
     , testCase "Design |-  ok,x,y,z :: S,M  -- shouldn't match."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [ok,x,y,z])
            (lwrap [lS,lM])
         @?= Nothing )
     , testCase "Design |-  x,y,z,ok :: M,S  -- shouldn't match."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x,y,z,ok])
            (lwrap [lM,lS])
         @?= Nothing )
     , testCase "Design  |-  ok,S :: O  -- matches at least once."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [ok] ++lwrap [lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [ok] ++lwrap [lS]) emptyBinding
           :: [Binding] ) )
     , testCase "Design  |-  ok :: M,S  -- shouldn't match."
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [ok] )
            (lwrap [lM,lS])
         @?= Nothing )
     , testCase "|-  x,y :: O  -- matches at least once."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [x,y]) emptyBinding :: [Binding] ) )
     , testCase "|-  x,y' :: O  -- matches at least once."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y'])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [x,y']) emptyBinding :: [Binding] ) )
     , testCase "|-  e,x :: O  -- matches at least once."
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [e,x])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [e,x]) emptyBinding :: [Binding] ) )
     , testCase "Design  |-  {x,y,z} :: {S'}  -- shouldn't match."
       ( vsMatch [vtDesign] emptyBinding S.empty S.empty
            (S.fromList $ vwrap [x,y,z])
            (S.fromList $ lwrap [lS'])
         @?= Nothing )
     , testCase "Design  |-  {x,y,z} :: {S}  -- matches at least once."
       ( vsMatch [vtDesign] emptyBinding S.empty S.empty
            (S.fromList $ vwrap [x,y,z])
            (S.fromList $ lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ) )
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
