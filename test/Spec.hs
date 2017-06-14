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

test_ident_fail =  ident "42" @?= Nothing
test_ident_ok   =  idName (fromJust $ ident "forty2") @?= "forty2"


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
 = [ testGroup "HUnit Ident"
     [
       testCase "Ident should Fail" test_ident_fail
    ,  testCase "Ident is OK" test_ident_ok
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
