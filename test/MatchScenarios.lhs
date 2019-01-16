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
import Data.List (nub, sort, (\\))

import Test.HUnit
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import NiceSymbols
import Utilities
import LexBase
import Variables
import AST
import VarData
import Binding
import Matching
import MkTestBind
import TestRendering
\end{code}

\newpage
\subsection{Matching Scenario Introduction}

We create high-level matching scenarios to test the
fitness for purpose of the matching algorithms.
We place particular emphasis on UTP-specific matching requirements.

Here is our initial set of scenarios:
\begin{description}
  \item [Reserved List-Variables] $O$, $M$, and $S$.
  \item[($O$,$S$,$M$)-matching]~\\
    Matching, \emph{e.g.}, $\exists ok_m,S_m \bullet \ldots$
    against $\exists O_n \bullet \ldots$
    yields $O_n \mapsto \setof{ok_m} \cup S_m$.
  \item[Universal Instantiation]
   $$
     (\forall \lst x,\lst y \bullet P)
     \implies
     (\forall \lst y \bullet P[\lst e/\lst x])
     , \quad \lst x \notin P
   $$
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

\textbf{
NEED AN EXAMPLE OF AN OPERATIONAL SEMANTICS RULE
THAT REQUIRES MATCHING AGAINST ``PROGRAM TEXTS.''
}

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
lv ->> vl  =  fromJust . addKnownVarList (varOf lv) (lwrap vl)
lv -.> vl  =  fromJust . addKnownVarList (varOf lv) (vwrap vl)
lv -~> vs  =  fromJust . addKnownVarSet  (varOf lv) (vswrap vs)
lv ~~> vs  =  fromJust . addKnownVarSet  (varOf lv) (lswrap vs)
\end{code}

\subsubsection{Pre-defined Types}

We assume the existence of types
for boolean ($\Bool$)
and integer ($\Int$) values.
\begin{code}
bool = GivenType $ jId $ _mathbb "B"
int  = GivenType $ jId $ _mathbb "Z"
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

vtL_Design =  lO ->> [lM,lS] $ lS -.> [x,y,z] $ lM -.> [ok] $ kvDesign

vtS_Design  =  lO ~~> [lM,lS] $ lS -~> [x,y,z] $ lM -~> [ok] $ kvDesign
\end{code}

\newpage
\subsubsection{Reserved List-Variable Tests}

\begin{code}
e = PreExpr $ jId "e"
okn = MidVar k "n" ; xn = MidVar ex "n" ; yn = MidVar wy "n" ; zn = MidVar ze "n"
lOn = MidVars o "n" ; lMn = MidVars m "n" ; lSn = MidVars s "n"

test_reserved_listvars
 = testGroup "Reserved List Variables"
     [ test_none_reserved, test_reserved_as_lists
     , test_reserved_as_sets, test_less_reserved ]

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
     , testCase "|-  e,x :: O  -- succeeds ."
       ( vlMatch [] emptyBinding S.empty S.empty (vwrap [e,x]) (lwrap [lO])
         @?=
         ( bindLVarToVList lO (vwrap [e,x]) emptyBinding :: [Binding] ) )
     ]

lSu  = lS `less` ([u],[])
lSuw = lS `less` ([u,w],[])
lSuvw = lS `less` ([u,v,w],[])
lOu = lO `less` ([u],[])

u = jId "u"  ;  vu = PreVar u  ;  gu = StdVar vu
vv = PreVar v  ; gv = StdVar vv
w = jId "w"  ;  vw = PreVar w  ;  gw = StdVar vw



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
     , testCase "L_Design |- [x,y,z] :: [u,S\\u] -- succeeds"
         ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
             (vwrap [x,y,z]) (vwrap [vu] ++ lwrap [lSu])
           @?= [ bindVV gu gx $ bindLl (LstVar lSu) [gy,gz] emptyBinding
               ]
         )
     , testCase "L_Design |- [x,y,z] :: [S\\u, u] -- SHOULD SUCCEED (TRICKY!)"
         ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
             (vwrap [x,y,z]) (lwrap [lSu] ++ vwrap [vu])
           @?= [ bindVV gu gz $ bindLl (LstVar lSu) [gx,gy] emptyBinding
               ]
         )
     , testCase "L_Design |- [y,z,x] :: [S\\u, u] -- SHOULD SUCCEED (TRICKY!)"
         ( vlMatch [vtL_Design] emptyBinding S.empty S.empty
             (vwrap [y,z,x]) (lwrap [lSu] ++ vwrap [vu])
           @?= [ bindVV gu gx $ bindLl (LstVar lSu) [gy,gz] emptyBinding
               ]
         )
     , testCase "L_Design |- [x,y,z] :: [u,w,S\\uw] -- succeeds"
         ( nub (vlMatch [vtL_Design] emptyBinding S.empty S.empty
                  (vwrap [x,y,z]) (vwrap [vu,vw] ++ lwrap [lSuw]))
           @?= [ bindVV gu gx $ bindVV gw gy
                 $ bindLl (LstVar lSuw) [gz] emptyBinding
               ]
         )
     , testCase "L_Design |- [x,y,z] :: [u,S\\uw,w] -- succeeds"
         ( nub (vlMatch [vtL_Design] emptyBinding S.empty S.empty
                  (vwrap [x,y,z]) (vwrap [vu] ++ lwrap [lSuw] ++ vwrap [vw]))
           @?= [ bindVV gu gx $ bindVV gw gz
                 $ bindLl (LstVar lSuw) [gy] emptyBinding
               ]
         )
     , testCase "L_Design |- [z,y,x] :: [u,S\\uw,w] -- succeeds"
         ( nub (vlMatch [vtL_Design] emptyBinding S.empty S.empty
                  (vwrap [z,y,x]) (vwrap [vu] ++ lwrap [lSuw] ++ vwrap [vw]))
           @?= [ bindVV gu gz $ bindVV gw gx
                 $ bindLl (LstVar lSuw) [gy] emptyBinding
               ]
         )
     , testCase "L_Design |- [y,x,z] :: [u,S\\uw,w] -- succeeds"
         ( nub (vlMatch [vtL_Design] emptyBinding S.empty S.empty
                  (vwrap [y,x,z]) (vwrap [vu] ++ lwrap [lSuw] ++ vwrap [vw]))
           @?= [ bindVV gu gy $ bindVV gw gz
                 $ bindLl (LstVar lSuw) [gx] emptyBinding
               ]
         )
     , testCase "L_Design |- [ok,S\\u] :: [O\\u] -- succeeds"
         ( nub (vlMatch [vtL_Design] emptyBinding S.empty S.empty
                  (vwrap [ok]++lwrap [lSu]) (lwrap [lOu]))
           @?= [ bindLl (LstVar lOu) (vwrap [ok]++lwrap [lSu])
                 $ bindVV gu gz emptyBinding
               ]
         )
     , testCase "L_Design |- [e] :: [e,S\\uvw] -- succeeds"
         ( nub (vlMatch [vtL_Design] emptyBinding S.empty S.empty
                    [ge] (ge:lwrap [lSuvw]))
           @?= [ bindVV ge ge $ bindVV gu gx $ bindVV gv gy $ bindVV gw gz
                 $ bindLl (LstVar lSuvw) [] emptyBinding
               ]
         )
   ]


test_reserved_as_sets
 = testGroup "O,M,S reserved as {ok,x,y,z}"
     [ testCase "S_Design |-  x,y,z :: S  -- fails."
       ( vlMatch [vtS_Design] emptyBinding S.empty S.empty
            (vwrap [x,y,z])
            (lwrap [lS])
         @?= Nothing )
     , testCase "S_Design |-  {x,y,z} :: {S}  -- matches at least once."
       ( nub (vsMatch [vtS_Design] emptyBinding S.empty S.empty
                       (vswrap [x,y,z])
                       (lswrap [lS]))
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
\end{code}
\newpage
\begin{code}
test_less_reserved
 = testGroup "S reserved as {x,y,z}, less x,y,z or more" -- []
     [ testCase "S_Design |- {x,y,z} :: {u,S\\u} -- SHOULD BE 3 WAYS"
        ( nub ( vsMatch [vtS_Design] emptyBinding S.empty S.empty
                   (vswrap [x,y,z])
                   (vswrap [vu] `S.union` lswrap [lS `less` ([u],[])]) )
          @?= [ bindVV gu gz $ bindLs (LstVar lSu) [gx,gy] emptyBinding
              ]
        )
     , testCase "S_Design |- {x,y,z} :: {u,w,S\\u,w} -- SHOULD BE 6 WAYS"
        ( nub (vsMatch [vtS_Design] emptyBinding S.empty S.empty
            (vswrap [x,y,z])
            (vswrap [vu,vw] `S.union` lswrap [lS `less` ([u,w],[])]) )
          @?= [ bindVV gu gy $ bindVV gw gz
                $ bindLs (LstVar lSuw) [gx] emptyBinding
              ]
        )
     , testCase "S_Design |- {x,y,z} :: {u,v,w,S\\u,v,w} -- SHOULD BE 6 WAYS"
        ( nub (vsMatch [vtS_Design] emptyBinding S.empty S.empty
            (vswrap [x,y,z])
            (vswrap [vu,vv,vw] `S.union` lswrap [lS `less` ([u,v,w],[])]) )
          @?= [ bindVV gu gx $ bindVV gv gy $ bindVV gw gz
                $ bindLs (LstVar lSuvw) [] emptyBinding
              ]
        )
     ]

tstNoneReserved = defaultMain [test_none_reserved]
tstListReserved = defaultMain [test_reserved_as_lists]
tstSetReserved  = defaultMain [test_reserved_as_sets]
tstLessReserved = defaultMain [test_less_reserved]
tstReserved     = defaultMain [test_reserved_listvars]
\end{code}

\newpage
\subsection{Universal Instantiation}

We have a generalised form of the usual instantation axiom
for the universal quantifier:
$$
 (\forall \lst x,\lst y \bullet P)
 \implies
 (\forall \lst y \bullet P[\lst e/\lst x])
 , \quad \lst x \notin P
$$

We need $\lst x$ and $\lst y$
\begin{code}
xs = LVbl x [] [] ; ys = LVbl y [] []
gxs = LstVar xs ; gys = LstVar ys
xsys = S.fromList [gxs,gys]
\end{code}

%\newpage
\subsubsection{Sequential Composition Tests}


\begin{code}
set = S.fromList

test_instantiation
  = testGroup "Instantiation"
    [ testCase "{x$,y$} :: {x$,y$} - succeeds 3 ways"
       ( set ( vsMatch [] emptyBinding S.empty S.empty xsys xsys )
         @?= set [ bindLs gxs [gxs] $ bindLs gys [gys]  $ emptyBinding
                 , bindLs gxs [gxs,gys] $ bindLs gys [] $ emptyBinding
                 , bindLs gxs [] $ bindLs gys [gxs,gys] $ emptyBinding
                 ]
       )
    ]


tstInst = defaultMain [test_instantiation]
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
semi = jId ";"
exists = jId _exists
land = jId _land

p `seqComp` q = PCons semi [p,q]
eX vs p = fromJust $ pBind exists (S.fromList $ vs) p
p `lAnd` q = PCons land [p,q]
\end{code}

Also we need to insert our known variables and
list-variables into general-vars:
\begin{code}
gok = StdVar ok ; gok' = StdVar ok' ; gokm = StdVar okm
gx  = StdVar x  ; gx'  = StdVar x'  ; gxm  = StdVar xm
gy  = StdVar y  ; gy'  = StdVar y'  ; gym  = StdVar ym
gz  = StdVar z  ; gz'  = StdVar z'  ; gzm  = StdVar zm
gO  = LstVar lO ; gO'  = LstVar lO' ; gOm  = LstVar lOm  ; gOn = LstVar lOn
gM  = LstVar lM ; gM'  = LstVar lM' ; gMm  = LstVar lMm  ; gMn = LstVar lMn
gS  = LstVar lS ; gS'  = LstVar lS' ; gSm  = LstVar lSm  ; gSn = LstVar lSn
\end{code}

We also need some predicates to throw around ($P$, $Q$):
\begin{code}
vp = PredVar (jId "P") Static ; gvp = StdVar vp
p = fromJust $ pVar vp
vq = PredVar (jId "Q") Static ; gvq = StdVar vq
q = fromJust $ pVar vq

-- builder for exists Om @ P[...] /\ Q[...]
eOpAqm = eOpAq "m" ; eOpAqn = eOpAq "n"
eOpAq n = eX [gvDurRen n gOm] (endO2mid n p `lAnd` begO2mid n q)
endO2mid n p = PSub p $ fromJust $ substn [] [(lO',lvDurRen n lOm)]
begO2mid n p = PSub p $ fromJust $ substn [] [(lO,lvDurRen n lOm)]

-- builder for exists Mm,Sm @ P[...] /\ Q[...]
eMSpAqm = eMSpAq "m" ; eMSpAqn = eMSpAq "n"
eMSpAq n
 = eX [gvDurRen n gMm,gvDurRen n gSm] (endMS2mid n p `lAnd` begMS2mid n q)
endMS2mid n p
  = PSub p $ fromJust $ substn [] [(lM',lvDurRen n lMm),(lS',lvDurRen n lSm)]
begMS2mid n p
  = PSub p $ fromJust $ substn [] [(lM,lvDurRen n lMm),(lS,lvDurRen n lSm)]

-- builder for exists ok,Sm @ P[...] /\ Q[...]
eoSpAqm = eoSpAq "m" ; eoSpAqn = eoSpAq "n"
eoSpAq n
 = eX [gvDurRen n gokm,gvDurRen n gSm] (endoS2mid n p `lAnd` begoS2mid n q)
endoS2mid n p
  = PSub p $ fromJust $ substn [(ok',evar bool $ vDurRen n okm)] [(lS',lvDurRen n lSm)]
begoS2mid n p
  = PSub p $ fromJust $ substn [(ok,evar bool $ vDurRen n okm)] [(lS,lvDurRen n lSm)]

evar t v = fromJust $ eVar t v
\end{code}


\newpage
\subsubsection{Sequential Composition Tests}

We start with some substitution tests:
\begin{code}
sub_O = fromJust $ substn [] [(lO,lOm)]
sub_ok_S = fromJust $ substn [(ok,evar bool okm)] [(lS,lSm)]
sub_okxyz
 = fromJust $ substn
    [ (ok,evar bool okm)
    , (x,evar int xm), (y,evar int ym), (z,evar int zm)
    ] []

test_substitution
 = testGroup "Substitutions"
    [ testCase "[okm,Sm/ok,S] :: [Om/O] - succeeds"
       ( nub (sMatch [vtS_Design] emptyBinding S.empty S.empty sub_ok_S sub_O)
        @?= [ bindLs gO [gok,gS] $ bindLs gOm [gokm,gSm] $ emptyBinding ] )
    , testCase "[okm,xm,ym,zm/ok,x,y,z] :: [Om/O] - succeeds"
       (nub (sMatch [vtS_Design] emptyBinding S.empty S.empty sub_okxyz sub_O)
        @?= [ bindLs gO [gok,gx,gy,gz] $ bindLs gOm [gokm,gxm,gym,gzm] $ emptyBinding ] )
    , testCase "[okm,xm,ym,zm/ok,x,y,z] :: [okm,Sm/ok,S] - succeeds"
       (nub (sMatch [vtS_Design] emptyBinding S.empty S.empty sub_okxyz sub_ok_S)
        @?= [ bindVV gok gok $ bindVV gokm gokm $
              bindLs gS [gx,gy,gz] $ bindLs gSm [gxm,gym,gzm] $
              emptyBinding ] )
    ]

tstSub = defaultMain [test_substitution]
\end{code}

Now, the compositions:
\begin{code}
smBinding
 = bindVV gvp gvp $ bindVV gvq gvq $
      bindLS gO gO $ bindLS gO' gO' $ bindLS gOm gOm $
      emptyBinding

seeSMB = seeBind smBinding

test_composition
 = testGroup "Composition"
    [ testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches itself"
       (nub( tMatch [vtS_Design] emptyBinding S.empty S.empty eOpAqm eOpAqm )
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLS gO gO $ bindLS gO' gO' $ bindLS gOm gOm $
              emptyBinding] )

    , testCase "P[Om/O'] matches itself"
       (nub ( tMatch [vtS_Design] emptyBinding S.empty S.empty
                                            (endO2mid "m" p) (endO2mid "m" p) )
        @?= [ bindVV gvp gvp $ bindLS gOm gOm $ emptyBinding ] )
    , testCase "Q[Om/O] matches itself"
       (nub ( tMatch [vtS_Design] emptyBinding S.empty S.empty
                                            (begO2mid "m" q) (begO2mid "m" q) )
        @?= [ bindVV gvq gvq $ bindLS gOm gOm $ emptyBinding ] )

    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when n replaces m"
       (nub ( tMatch [vtS_Design] emptyBinding S.empty S.empty eOpAqn eOpAqm )
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLS gO gO $ bindLS gO' gO' $ bindLS gOm gOn $
              emptyBinding] )
    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when M,S replaces O"
       (nub ( tMatch [vtS_Design] emptyBinding S.empty S.empty eMSpAqm eOpAqm )
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLs gO [gM,gS] $ bindLs gO' [gM',gS'] $ bindLs gOm [gMm,gSm] $
              emptyBinding] )
    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when M,S;n replaces O;m"
       (nub ( tMatch [vtS_Design] emptyBinding S.empty S.empty eMSpAqn eOpAqm )
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLs gO [gM,gS] $ bindLs gO' [gM',gS'] $ bindLs gOm [gMn,gSn] $
              emptyBinding] )
    , testCase "E Om @ P[Om/O'] /\\ Q[Om/O] matches when ok,S replaces O"
       (nub ( tMatch [vtS_Design] emptyBinding S.empty S.empty eoSpAqm eOpAqm )
        @?= [ bindVV gvp gvp $ bindVV gvq gvq $
              bindLs gO [gok,gS] $ bindLs gO' [gok',gS'] $ bindLs gOm [gokm,gSm] $
              emptyBinding] )
    ]

tstComp = defaultMain [test_composition]

test_sequential_composition
 = testGroup "Defn. of Sequential Composition"
     [ test_substitution, test_composition]
\end{code}

\newpage
\subsection{Assignment}

    $$
      x := e
      ~\defs~
      ok \implies ok' \land x' = e \land S'\less x = S\less x
    $$

We start with syntax definitions of assignment, equality
and implication.
\begin{code}
asg = jId ":="
implies = jId _implies
eq = jId "="

v .:= e        =  PCons asg [fromJust $ eVar ArbType $ ScriptVar v, e]
p `impl` q     =  PCons implies [p,q]
e1 `equal` e2  =  PCons eq [e1,e2]
\end{code}

Now, turning $ok$ into a term, subtracting from list-variables,
and defining assigment
\begin{code}
tok = fromJust $ eVar bool ok ; tok' = fromJust $ eVar bool ok'

(LVbl v is ij) `less` (iv,il)
 = LVbl v (nub $ sort (is++iv)) (nub $ sort (is++il))

v `assigned` e
  = tok `impl` PCons land [ tok' , v' `equal` e ,  _S_v'_is_S_v ]
  where
    v' = fromJust $ eVar ArbType $ PostVar v
    _S_v'_is_S_v = PIter land eq [lS' `less` ([v],[]), lS `less` ([v],[])]
\end{code}

Test values:
\begin{code}
v = jId "v"
vtv = ScriptVar v
gtv = StdVar vtv
sy = ScriptVar wy
gsy = StdVar sy
ee = fromJust $ eVar int e
ge = StdVar e
e42 = EVal int $ Integer 42
\end{code}

\subsubsection{Assignment Tests}

\begin{code}
test_assignment
 = testGroup "Assignment"
    [ test_simple_assignment, test_simultaneous_assignment ]

test_simple_assignment
 = testGroup "Simple Assignment (<< ... >> denotes definition expansion)"
    [ testCase "Design |- y := 42  :: v := e, should succeed"
       ( tMatch [vtS_Design] emptyBinding S.empty S.empty
           (wy .:= e42) (v .:= ee)
           @?= (Just $ bindVV gtv gsy $ bindVT ge e42 $ emptyBinding)
       )
    , testCase "Design |- << y := 42 >> :: << v := e >>, should succeed"
       ( tMatch [vtS_Design] emptyBinding S.empty S.empty
           (wy `assigned` e42) (v `assigned` ee)
           @?= ( Just $ bindVV gtv gsy $ bindVT ge e42
               $ bindVV gok gok $ bindVV gok' gok'
               $ bindLL (LstVar (lS  `less` ([v],[])))
                        (LstVar (lS  `less` ([wy],[])))
               $ bindLL (LstVar (lS' `less` ([v],[])))
                        (LstVar (lS' `less` ([wy],[])))
               $ emptyBinding )
       )
    ]
\end{code}

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
\begin{code}
vs `simasgn` es
  = PCons land [ PIter land eq [vs', es]
               , PIter land eq [lS' `less` ([],[vs]), lS `less` ([],[vs])] ]
  where vs' = PostVars vs


vs_becomes_es = v `simasgn` (LVbl e [] [])
es    = LVbl e [] []         ; ges   = LstVar es
vs'   = PostVars v           ; gvs'  = LstVar vs'
lSvs  = lS `less` ([],[v])   ; gSvs  = LstVar lSvs
lS'vs = lS' `less` ([],[v])  ; gS'vs = LstVar lS'vs
lSzs  = lS `less` ([],[ze])  ; gSzs  = LstVar lSzs
lS'zs = lS' `less` ([],[ze]) ; gS'zs = LstVar lS'zs

f = PreExpr $ jId "f"

us_becomes_fs = u `simasgn` (LVbl f [] [])
fs    = LVbl f [] []        ; gfs   = LstVar fs
us'   = PostVars u          ; gus'  = LstVar us'
lSus  = lS `less` ([],[u])  ; gSus  = LstVar lSus
lS'us = lS' `less` ([],[u]) ; gS'us = LstVar lS'us

e1 = EVal int $ Integer 1
e2 = EVal int $ Integer 2

tx' = fromJust $ eVar int x'
ty' = fromJust $ eVar int y'

x'1y'2 = ((evar int x' `equal` e1) `lAnd` (evar int y' `equal` e2))
       `lAnd`
       (PIter land eq [lS' `less` ([],[ze]),lS `less` ([],[ze])])

test_simultaneous_assignment
 = testGroup "Simultaneous Assignment"
     [ testCase "<< v$ := e$>> :: << v$ := e$>>"
         ( tMatch [vtS_Design] emptyBinding S.empty S.empty
                  vs_becomes_es vs_becomes_es
           @?= ( Just $ bindLL gvs' gvs' $ bindLL ges ges
                $ bindLL gSvs gSvs $ bindLL gS'vs gS'vs $ emptyBinding ) )
     , testCase "<< u$ := f$>> :: << v$ := e$>>"
         ( tMatch [vtS_Design] emptyBinding S.empty S.empty
                  us_becomes_fs vs_becomes_es
           @?= ( Just $ bindLL gvs' gus' $ bindLL ges gfs
                $ bindLL gSvs gSus $ bindLL gS'vs gS'us $ emptyBinding ) )
     , testCase "(x'=1 /\\ y'=2) /\\ S'\\z = S\\z  :: << v$ := e$>>"
         ( tMatch [vtS_Design] emptyBinding S.empty S.empty
                  x'1y'2 vs_becomes_es
           @?= ( Just $ bindLt gvs' [tx',ty'] $ bindLt ges [e1,e2]
                $ bindLL gSvs gSzs $ bindLL gS'vs gS'zs $ emptyBinding ) )
     ]

tstAsg = defaultMain [test_assignment]
\end{code}

\newpage
\subsection{Exported Tests}
\begin{code}
test_match_scenarios :: [TF.Test]

test_match_scenarios
  = [ testGroup "\nMatching Scenarios"
       [ test_reserved_listvars
       , test_instantiation
       , test_sequential_composition
       , test_assignment
       ]
    ]

tstMatchScenarios = defaultMain test_match_scenarios
\end{code}
