{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck ((==>))

import Data.Maybe

import AST

{- HUnit Tests -}

test_CT = ast_tst_CT @?= ast_res_CT
test_TC = ast_tst_TC @?= ast_res_TC
test_cc = ast_tst_cc @?= ast_res_cc
test_c1c2 = ast_tst_c1c2 @?= ast_res_c1c2
test_NN = ast_tst_NN @?= ast_res_NN
test_N1N2 = ast_tst_N1N2 @?= ast_res_N1N2
test_N2N1 = ast_tst_N2N1 @?= ast_res_N2N1

{- QuickCheck Tests -}


{-
 prop_ident str
  =  validIdent str
     ==>
     idName (fromJust $ ident str) @?= str
-}

{- Test Main -}

main = defaultMain tests

tests :: [TF.Test]
tests
 = [ testGroup "\nSide Condition Conflicts"
     [
       testCase "TrueC is right-identity" test_CT
     , testCase "TrueC is left-identity" test_TC
     , testCase "IsCond is self-Idempotent" test_cc
     , testCase "IsCond is Independent" test_c1c2
     , testCase "Fresh is self-Idempotent" test_NN
     , testCase "Fresh merges with Union (1)" test_N1N2
     , testCase "Fresh merges with Union (2)" test_N2N1
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
