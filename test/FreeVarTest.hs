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

import TestRendering


-- -----------------------------------------------------------------------------
tst_group1 :: TF.Test


tst_group1
 = testGroup "group1"
     [ testCase "1+1=2"
       ( 1+1
         @?= 2 )
     ]


-- -----------------------------------------------------------------------------
tst_FreeVar :: [TF.Test]
tst_FreeVar
  = [ testGroup "\nFreeVar"
      [ tst_group1
      ]
    ]
