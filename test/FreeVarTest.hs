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
import FreeVars
import TestRendering

import TestDefs


-- -----------------------------------------------------------------------------

tx = jVar eint x ; tx' = jVar eint x' ; txm = jVar eint xm ;
tP = jVar P $ PredVar (jId "P") Static

e42plus x = Cons eint (jId "+")[e42,x]

univ = Cls (jId "[]")
univP = univ tP

tP1 = jVar P $ PredVar (jIdU "P" 1) Static
univP1 = univ tP1

-- -----------------------------------------------------------------------------
tst_normNoQ :: TF.Test
tst_normNoQ
 = testGroup "normalise(No)Quantifiers"
     [ testCase "normQ 42 = 42" ( normaliseQuantifiers e42 @?= e42 )
     , testCase "normQ x = x" ( normaliseQuantifiers tx @?= tx )
     , testCase "normQ x' = x'" ( normaliseQuantifiers tx' @?= tx' )
     , testCase "normQ x_m = x_m" ( normaliseQuantifiers txm @?= txm )
     , testCase "normQ P = P" ( normaliseQuantifiers tP @?= tP )
     , testCase "normQ (42+x) = 42+x"
        (normaliseQuantifiers (e42plus tx) @?= (e42plus tx))
     -- Cls, Sub, Iter, Typ
     ]

-- -----------------------------------------------------------------------------
tst_normWithQ :: TF.Test
tst_normWithQ
 = testGroup "normalise(With)Quantifiers"
     [ testCase "normQ [P_0] = [P_1]"
       ( normaliseQuantifiers univP @?= univP1 )
     ]


-- -----------------------------------------------------------------------------
tst_FreeVar :: [TF.Test]
tst_FreeVar
  = [ testGroup "\nFreeVar"
      [ tst_normNoQ
      , tst_normWithQ
      ]
    ]
