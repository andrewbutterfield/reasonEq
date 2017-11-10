\section{Match Scenarios}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module MatchScenarios ( test_match_scenarios ) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub, sort)

import Test.HUnit
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Utilities
import LexBase
import AST
import VarData
import Binding
import Matching
import MkTestBind
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
  \item[Skip]
    \begin{eqnarray*}
      \Skip &\defs& ok \implies ok' \land S'=S
    \end{eqnarray*}
    A simple form of a simple simultaneous assignment!
\end{description}

\subsection{Pre-defined Values and Builders}

\subsubsection{Pre-defined Table Builders}

The builders are designed to work with ``safe'' arguments
and will exhibit runtime failures if used improperly.
\begin{code}
jId = fromJust . ident
vwrap = map StdVar ;  vswrap = S.fromList . vwrap
lwrap = map LstVar ;  lswrap = S.fromList . lwrap
v  ^=   t  =  fromJust . addKnownConst   v  t
v  .:.  t  =  fromJust . addKnownVar     v  t
lv ->> vl  =  fromJust . addKnownVarList lv (lwrap vl)
lv -.> vl  =  fromJust . addKnownVarList lv (vwrap vl)
lv -~> vs  =  fromJust . addKnownVarSet  lv (vswrap vs)
lv ~~> vs  =  fromJust . addKnownVarSet  lv (lswrap vs)
\end{code}

\subsubsection{Pre-defined Types}

We assume the existence of types
for boolean ($\Bool$)
and integer ($\Int$) values.
\begin{code}
bool = GivenType $ jId "B"
int  = GivenType $ jId "Z"
\end{code}


\newpage
\subsection{Reserved List-Variables}

We shall assume an imperative language with three program variables,
$x$, $y$, and $z$, and model observations $ok$ and $ok'$.

\subsubsection{Observation Variables}

Model observations regarding termination.
\begin{eqnarray*}
   ok, ok'         &:&   \Bool
\end{eqnarray*}
\begin{code}
k = jId "ok"
ok = PreVar k ; ok' = PostVar k ; okm = MidVar k "m"
\end{code}

Script observations regarding values of program variables.
\begin{eqnarray*}
   x,x',y,y',z,z'  &:&   \Int
\end{eqnarray*}
\begin{code}
ex = jId "x"  ;  x = PreVar ex  ;  x' = PostVar ex  ;  xm = MidVar ex "m"
wy = jId "y"  ;  y = PreVar wy  ;  y' = PostVar wy  ;  ym = MidVar wy "m"
ze = jId "z"  ;  z = PreVar ze  ;  z' = PostVar ze  ;  zm = MidVar ze "m"
\end{code}

\subsubsection{Observation Classifiers}

List-variables that classify observations.
\begin{eqnarray*}
   S \defs \setof{x,y,z} && S' \defs \setof{x',y',z'}
\\ M \defs \setof{ok}    && M' \defs \setof{ok'}
\\ O \defs M \cup S      && O' \defs M'\cup S'
\end{eqnarray*}
\begin{code}
s = jId "S"  ;  lS = PreVars s  ;  lS' = PostVars s  ;  lSm = MidVars s "m"
m = jId "M"  ;  lM = PreVars m  ;  lM' = PostVars m  ;  lMm = MidVars m "m"
o = jId "O"  ;  lO = PreVars o  ;  lO' = PostVars o  ;  lOm = MidVars o "m"
\end{code}

\subsubsection{``Design'' Variable-Table}

We have two variants,
one which defines $O$, $S$ and $M$ in terms of lists,
the other doing it in terms of sets.
\begin{code}
kvDesign =
    ok .:. bool $ ok' .:. bool
  $  x .:. int  $  x' .:. int  $ y .:. int $ y' .:. int $ z .:. int $ z' .:. int
  $ newVarTable

vtL_Design =
    lS -.> [x,y,z] $ lS' -.> [x',y',z'] $ lSm -.> [xm,ym,zm]
  $ lM -.> [ok]    $ lM' -.> [ok']      $ lMm -.> [okm]
  $ lO ->> [lM,lS] $ lO' ->> [lM',lS']  $ lOm ->> [lMm,lSm]
  $ kvDesign

vtS_Design =
    lS -~> [x,y,z] $ lS' -~> [x',y',z'] $ lSm -~> [xm,ym,zm]
  $ lM -~> [ok]    $ lM' -~> [ok']      $ lMm -~> [okm]
  $ lO ~~> [lM,lS] $ lO' ~~> [lM',lS']  $ lOm ~~> [lMm,lSm]
  $ kvDesign
\end{code}

\newpage
\subsubsection{Reserved List-Variable Tests}

\begin{code}
e = PreExpr $ jId "e"
okn = MidVar k "n" ; xn = MidVar ex "n" ; yn = MidVar wy "n" ; zn = MidVar ze "n"
lOn = MidVars o "n" ; lMn = MidVars m "n" ; lSn = MidVars s "n"

test_reserved_listvars
 = testGroup "Reserved List Variables"
     [test_none_reserved, test_reserved_as_lists, test_reserved_as_sets]

test_none_reserved
 = testGroup "O,M,S not reserved"
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
     , testCase "|-  M,S :: O  -- matches ."
       ( vlMatch [] emptyBinding S.empty S.empty
            (lwrap [lM,lS])
            (lwrap [lO])
         @?=
         ( bindLVarToVList lO (lwrap [lM,lS]) emptyBinding :: [Binding] ) )
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

test_reserved_as_lists
 = testGroup "O,M,S reserved as [ok,x,y,z]"
     [ testCase "L_Design |-  x,y,z :: S  -- matches."
       ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= ( bindLVarToVList lS (vwrap [x,y,z]) emptyBinding :: [Binding] ))
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
     ]

test_reserved_as_sets
 = testGroup "O,M,S reserved as {ok,x,y,z}"
     [ testCase "S_Design |-  x,y,z :: S  -- fails."
       ( vlMatch [vtS_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "S_Design |-  {x,y,z} :: {S}  -- matches at least once."
       ( vsMatch [vtS_Design] emptyBinding S.empty S.empty
            (vswrap [x,y,z])
            (lswrap [lS])
         @?= ( bindLVarToVSet lS (vswrap [x,y,z]) emptyBinding :: [Binding] ))
     , testCase "S_Design |-  {Om} :: {Om}  -- matches ."
       ( nub( vsMatch [vtS_Design] emptyBinding S.empty S.empty
                 (lswrap [lOm]) (lswrap [lOm]) )
         @?= ( bindLVarToVSet lOm (lswrap [lOm]) emptyBinding :: [Binding] ) )
     , testCase "S_Design |-  {On} :: {Om}  -- matches ."
       ( nub (vsMatch [vtS_Design] emptyBinding S.empty S.empty
                 (lswrap [lOn]) (lswrap [lOm]) )
         @?= ( bindLVarToVSet lOm (lswrap [lOn]) emptyBinding :: [Binding] ) )
     , testCase "S_Design |-  {Mm,Sm} :: {Om}  -- matches ."
       ( nub( vsMatch [vtS_Design] emptyBinding S.empty S.empty
                 (lswrap [lMm,lSm]) (lswrap [lOm]) )
         @?= ( bindLVarToVSet lOm (lswrap [lMm,lSm]) emptyBinding :: [Binding] ) )
     , testCase "S_Design |-  {Mn,Sn} :: {Om}  -- matches ."
       ( nub (vsMatch [vtS_Design] emptyBinding S.empty S.empty
                 (lswrap [lMn,lSn]) (lswrap [lOm]) )
         @?= ( bindLVarToVSet lOm (lswrap [lMn,lSn]) emptyBinding :: [Binding] ) )
     , testCase "S_Design |-  {okm,Sm} :: {Om}  -- matches ."
       (let okmlSm = S.fromList [StdVar okm, LstVar lSm] in
       ( nub( vsMatch [vtS_Design] emptyBinding S.empty S.empty
                 okmlSm (lswrap [lOm]) )
         @?= ( bindLVarToVSet lOm okmlSm emptyBinding :: [Binding] ) ))
     , testCase "S_Design |-  {okn,Sn} :: {Om}  -- matches ."
       (let oknlSn = S.fromList [StdVar okn, LstVar lSn] in
       ( nub (vsMatch [vtS_Design] emptyBinding S.empty S.empty
                 oknlSn (lswrap [lOm]) )
         @?= ( bindLVarToVSet lOm oknlSn emptyBinding :: [Binding] ) ))
     ]

tstNoneReserved = defaultMain [test_none_reserved]
tstListReserved = defaultMain [test_reserved_as_lists]
tstSetReserved  = defaultMain [test_reserved_as_sets]
tstReserved     = defaultMain [test_reserved_listvars]
\end{code}

\newpage
\subsection{Sequential Composition}

Consider the standard generic definition of sequential composition:
$$
    P ; Q
    ~\defs~
    \exists O_m \bullet P[O_m/O'] \land Q[O_m/O]
$$
We want to match here using the definitions regard $O$ and friends from above.


We need to define shorthands for
known predicate operators $;$, $\exists$ and $\land$.
\begin{code}
semi = jId "seqc"
exists = jId "exists"
land = jId "land"

p `seqComp` q = PCons semi [p,q]
eX vs p = fromJust $ pBind exists (S.fromList $ vs) p
p `lAnd` q = PCons land [p,q]
\end{code}

Also we need to insert our known list-variables into general-vars:
\begin{code}
gO = LstVar lO ; gO' = LstVar lO' ; gOm = LstVar lOm ; gOn = LstVar lOn
gM = LstVar lM ; gM' = LstVar lM' ; gMm = LstVar lMm ; gMn = LstVar lMn
gS = LstVar lS ; gS' = LstVar lS' ; gSm = LstVar lSm ; gSn = LstVar lSn
\end{code}

We also need some predicates to throw around ($P$, $Q$):
\begin{code}
vp = PredVar (jId "P") Static ; gvp = StdVar vp
p = fromJust $ pVar vp
vq = PredVar (jId "Q") Static ; gvq = StdVar vq
q = fromJust $ pVar vq
endO2mid n p = PSub p $ fromJust $ substn [] [(lO',lvDurRen n lOm)]
begO2mid n p = PSub p $ fromJust $ substn [] [(lO,lvDurRen n lOm)]
eOpAq n = eX [gvDurRen n gOm] (endO2mid n p `lAnd` begO2mid n q)
eOpAqm = eOpAq "m"
eOpAqn = eOpAq "n"
endMS2mid n p
  = PSub p $ fromJust $ substn [] [(lM',lvDurRen n lMm),(lS',lvDurRen n lSm)]
begMS2mid n p
  = PSub p $ fromJust $ substn [] [(lM,lvDurRen n lMm),(lS,lvDurRen n lSm)]
eMSpAq n
 = eX [gvDurRen n gMm,gvDurRen n gSm] (endMS2mid n p `lAnd` begMS2mid n q)
eMSpAqm = eMSpAq "m"
eMSpAqn = eMSpAq "n"
\end{code}


\subsubsection{Sequential Composition Tests}


\begin{code}
test_sequential_composition
 = testGroup "Sequential Composition"
    [ testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches itself"
       (tMatch [vtS_Design] emptyBinding S.empty S.empty eOpAqm eOpAqm
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLS gO gO $ bindLS gO' gO' $ bindLS gOm gOm $
              emptyBinding] )
    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when n replaces m"
       (tMatch [vtS_Design] emptyBinding S.empty S.empty eOpAqn eOpAqm
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLS gO gO $ bindLS gO' gO' $ bindLS gOm gOn $
              emptyBinding] )
    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when M,S replaces O"
       (tMatch [vtS_Design] emptyBinding S.empty S.empty eMSpAqm eOpAqm
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLs gO [gM,gS] $ bindLs gO' [gM',gS'] $ bindLs gOm [gMm,gSm] $
              emptyBinding] )
    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when M,S;n replaces O;m"
       (tMatch [vtS_Design] emptyBinding S.empty S.empty eMSpAqn eOpAqm
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLs gO [gM,gS] $ bindLs gO' [gM',gS'] $ bindLs gOm [gMn,gSn] $
              emptyBinding] )
    ]

tstSeqComp = defaultMain [test_sequential_composition]
\end{code}

\newpage
\subsection{Exported Tests}
\begin{code}
test_match_scenarios :: [TF.Test]

test_match_scenarios
  = [ testGroup "\nMatching Scenarios"
       [ test_reserved_listvars
       , test_sequential_composition
       ]
    ]

tstMatchScenarios = defaultMain test_match_scenarios
\end{code}
