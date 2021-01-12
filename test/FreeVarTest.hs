module FreeVarTest ( tst_FreeVar )
{-
Copyright  Andrew Buttefield (c) 2017-18

LICENSE: BSD3, see file LICENSE at reasonEq root
-}
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList, lookup, empty)
import Data.Set as S (fromList, singleton, empty)

import Test.HUnit
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import LexBase
import Variables
import AST
import Assertions
import FreeVars
import TestRendering

import TestDefs


-- -----------------------------------------------------------------------------

tx = jVar eint x ; tx' = jVar eint x' ; txm = jVar eint xm ;

tb = jVar earb b

bu u = Vbl (jIdU "b" u) ObsV Before
tbu u = jVar earb $ bu u

tP = jVar P $ PredVar (jId "P") Static
tPu u = jVar P $ PredVar (jIdU "P" u) Static

e42plus x = Cons eint (jId "+")[e42,x]
land p q = Cons P (jId "/\\") [p,q]

xs = LVbl x [] []
ys = LVbl y [] []
iterLVs = Iter P (jId "/\\") (jId "=") [xs,ys]

tInt = Typ int

subP =  Sub P tP sub42x_ysxs

sub42x_ysxs = jSub [(x,e42)] [(ys,xs)]

-- -----------------------------------------------------------------------------
tst_normNoQ :: TF.Test
tst_normNoQ
 = testGroup "normalise(No)Quantifiers"
     [ testCase "42            ~> 42            "
       ( normQTerm e42 @?= e42 )
     , testCase "x             ~> x             "
       ( normQTerm tx @?= tx )
     , testCase "x'            ~> x'            "
       ( normQTerm tx' @?= tx' )
     , testCase "x_m           ~> x_m           "
       ( normQTerm txm @?= txm )
     , testCase "P             ~> P             "
       ( normQTerm tP @?= tP )
     , testCase "(42+x)        ~> 42+x          "
       (normQTerm (e42plus tx) @?= (e42plus tx))
     , testCase "P[42,y$/x,x$] ~> P[42,y$/x,x$] "
       ( normQTerm subP @?= subP )
     , testCase "/\\(x$=y$)     ~> /\\(x$=y$)     "
       ( normQTerm iterLVs @?= iterLVs )
     , testCase "Int           ~> Int           "
       ( normQTerm tInt @?= tInt )
     ]

-- -----------------------------------------------------------------------------

univ = Cls (jId "[]")

univB = univ tb
tb1 = tbu 1 ; univB1 = univ tb1
tb2 = tbu 2 ; univB2 = univ tb2

univP = univ tP

exbTrue = jBnd P (jId "exists") (sngl $ StdVar b) tb
exbTrue1 = jBnd P (jId "exists") (sngl $ StdVar (bu 1)) tb1
exbTrue2 = jBnd P (jId "exists") (sngl $ StdVar (bu 2)) tb1
subP0b1 = Sub P tP $ jSubstn [(bu 0, tb1)] [(LVbl b [] [], LVbl (bu 1) [] [])]

tst_normWithQ :: TF.Test
tst_normWithQ
 = testGroup "normalise(With)Quantifiers"
     [ testCase "[b_0]                   ~> [b_1]                   "
       ( normQTerm univB @?= univB1 )
     , testCase "[[b_0]]                 ~> [[b_1]]                 "
       ( normQTerm (univ univB) @?= (univ univB1) )
     , testCase "[b_0 /\\ [b_0]]          ~> [b_1 /\\ [b_2]]          "
       ( normQTerm (univ (land tb univB))
          @?= (univ (land tb1 univB2)) )
      , testCase "[P_0]                   ~> [P_0]                   "
        ( normQTerm univP @?= univP )
      , testCase "[[P_0]]                 ~> [[P_0]]                 "
        ( normQTerm (univ univP) @?= (univ univP) )
      , testCase "[P_0 /\\ [P_0]]          ~> [P_0 /\\ [P_0]]          "
        ( normQTerm (univ (land tP univP))
           @?= (univ (land tP univP)) )
      , testCase "[b_0 /\\ P_0]            ~> [b_1 /\\ P_0[b_1/b_0]]   "
        ( normQTerm (univ (land tb tP)) @?= (univ (land tb1 subP0b1)) )
     -- pattern Bnd  tk n vs tm    <-  B tk n vs tm
     , testCase "exists b_0 @ b_0        ~> exists b_1 @ b_1        "
       ( normQTerm exbTrue @?= exbTrue1 )
     , testCase "b_0 /\\ exists b_0 @ b_0 ~> b_0 /\\ exists b_1 @ b_1 "
       ( normQTerm (land tb exbTrue) @?= (land tb exbTrue1) )
     -- pattern Lam  tk n vl tm    <-  L tk n vl tm
     ]


-- -----------------------------------------------------------------------------
tst_FreeVar :: [TF.Test]
tst_FreeVar
  = [ testGroup "\nFreeVar"
      [ tst_normNoQ
      , tst_normWithQ
      ]
    ]
