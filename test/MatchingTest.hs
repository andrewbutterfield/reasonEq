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
import Matching


-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

pv = ObsVar (fromJust $ ident "pv") Static
cv = ObsVar (fromJust $ ident "cv") Static

tst_Matching
  = [ testGroup "\nBinding (in Matching)"
      [ testGroup "lookupBind after bindVarToVar"
        [ testCase "pv -> cv"
          ( ( let (BindVar cv')
                    = fromJust (lookupBind
                                 (fromJust (bindVarToVar pv cv emptyBinding))
                                 pv )
              in cv'
            )
            @?=
            cv
          )
        ]
      ]
    , testGroup "\nMatching"
      [ testCase "1+1=2" (1+1 @?= 2)
      , testCase "2+2=5" (2+2 @?= 5)
      ]
    ]
