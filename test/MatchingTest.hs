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
      [ testCase "42 :: 42 (OK)"
        (match [] k42 k42 @?= [emptyBinding] )
      ]

-- -----------------------------------------------------------------------------
tst_tsMatch :: TF.Test

k58 = EVal ArbType $ Integer 58

lst = fromJust $ ident "lst" ; list ts = Cons P lst ts

l_42    = list [k42]
l_42_58 = list [k42,k58]
l_58_42 = list [k58,k42]

tst_tsMatch =
  testGroup "tsMatch (via match)"
      [ testCase "[42,58] :: [42,58] (OK)"
        (match [] l_42_58 l_42_58 @?= [emptyBinding] )
      , testCase "[42] :: [42,58] (FAIL)"
        (match [] l_42 l_42_58 @?= [] )
      , testCase "[42,58] :: [42] (FAIL)"
        (match [] l_42_58 l_42 @?= [] )
      , testCase "[42,58] :: [42] (FAIL)"
        (match [] l_42_58 l_58_42 @?= [] )
      ]

-- -----------------------------------------------------------------------------
tst_vMatch :: TF.Test

x = PreVar $ fromJust $ ident "x"
ex = EVar ArbType x

tst_vMatch =
  testGroup "vMatch (via match)"
      [ testCase "42 :: x (OK)"
        ( (match [] k42 ex :: [Binding] )
          @?= bindVarToTerm x k42 emptyBinding )
      ]

-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nMatching"
      [ tst_match
      , tst_tsMatch
      , tst_vMatch
      ]
    ]
