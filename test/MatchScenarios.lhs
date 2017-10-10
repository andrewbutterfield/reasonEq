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

vwrap = sort . map StdVar
lwrap = sort . map LstVar
akv v t tbl = fromJust $ addKnownVar v t tbl
aklv lv vl tbl = fromJust $ addKnownListVar lv vl tbl
\end{code}

Tests:
\begin{code}
tst_reserved_listvars
 = [ testGroup "Reserved List Variables"
     [ testCase "|-  x,y,z :: S  fails"
       ( vlMatch [] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "Design |-  x,y,z :: S  succeeds"
       ( vlMatch [vtDesign] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
       @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ))
     , testCase "x,y,z,S @ Design  |-  x,y,z :: S  succeeds"
       ( vlMatch [vtDesign] emptyBinding
            (S.fromList $ vwrap [x,y,z])
            (S.fromList $ lwrap [lS])
            (vwrap [x,y,z])
            (lwrap [lS])
       @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ))
     ]
   ]
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
