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



-- -----------------------------------------------------------------------------
tst_normQ :: TF.Test

tx = jVar eint x ; tx' = jVar eint x' ; txm = jVar eint xm ;

tst_normQ
 = testGroup "normaliseQuantifiers"
     [ testCase "normQ 42 = 42" ( normaliseQuantifiers e42 @?= e42 )
     , testCase "normQ x = x" ( normaliseQuantifiers tx @?= tx )
     , testCase "normQ x' = x'" ( normaliseQuantifiers tx' @?= tx' )
     , testCase "normQ x_m = x_m" ( normaliseQuantifiers txm @?= txm )
     ]

-- -----------------------------------------------------------------------------
tst_groupN :: TF.Test


tst_groupN
 = testGroup "groupN"
     [ testCase "1+1=2"
       ( 1+1
         @?= 2 )
     ]


-- -----------------------------------------------------------------------------
tst_FreeVar :: [TF.Test]
tst_FreeVar
  = [ testGroup "\nFreeVar"
      [ tst_normQ
      ]
    ]
