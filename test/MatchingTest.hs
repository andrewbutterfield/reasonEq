module MatchingTest ( tst_Matching )
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)

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

-- -----------------------------------------------------------------------------
tst_match :: TF.Test

k42 = EVal ArbType $ Integer 42

tst_match =
  testGroup "match"
      [ testCase "42 matches 42"
        (match [] k42 k42 @?= [emptyBinding] )
      ]

-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nMatching"
      [ tst_match
      ]
    ]
