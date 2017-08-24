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

-- ---------------
bindLook lkp bind pv cx
 = fromJust (lkp (fromJust (bind pv cx emptyBinding)) pv)

-- -----------------------------------------------------------------------------
tst_bindVarToVar :: TF.Test
vvBindLook = bindLook lookupBind bindVarToVar

pov = ObsVar (fromJust $ ident "pov") Static
cov = ObsVar (fromJust $ ident "cov") Static
pev = ExprVar (fromJust $ ident "pev") Static
ppv = PredVar (fromJust $ ident "ppv") Static

tst_bindVarToVar
  = testGroup "lookupBind after bindVarToVar"
      [ testCase "pov -> cov (Ok)"
        ( (let (BindVar cov')  = vvBindLook  pov cov in cov') @?= cov )
      , testCase "pev -> cov (Not Ok)"
        ( bindVarToVar pev cov emptyBinding @?= Nothing)
      , testCase "ppv -> cov (Not Ok)"
        ( bindVarToVar ppv cov emptyBinding @?= Nothing)
      ]

-- -----------------------------------------------------------------------------
tst_bindVarToTerm :: TF.Test
vtBindLook = bindLook lookupBind bindVarToTerm

ce42 = EVal ArbType $ Integer 42
pTrue = PVal $ Boolean True

tst_bindVarToTerm
  = testGroup "lookupBind after bindVarToTerm"
      [ testCase "pov -> 42 (Ok)"
        ( ( let (BindTerm ce42') = vtBindLook pov ce42 in ce42' ) @?= ce42 )
      , testCase "pov -> True (Not Ok)"
          ( bindVarToTerm pov pTrue emptyBinding @?= Nothing)
      , testCase "pev -> 42 (Ok)"
        ( ( let (BindTerm ce42') = vtBindLook pev ce42 in ce42' ) @?= ce42 )
      , testCase "pev -> True (Not Ok)"
            ( bindVarToTerm pev pTrue emptyBinding @?= Nothing)
      , testCase "ppv -> 42 (Not Ok)"
        ( bindVarToTerm ppv ce42 emptyBinding @?= Nothing)
      , testCase "ppv -> True (Ok)"
        ( ( let (BindTerm pTrue') = vtBindLook ppv pTrue in pTrue' ) @?= pTrue )
      ]

-- -----------------------------------------------------------------------------
tst_bindLVarToVList :: TF.Test
llBindLook = bindLook lookupLstBind bindLVarToVList

gpov = StdVar pov
gcov = StdVar cov
gpev = StdVar pev
gppv = StdVar ppv

polv = PreVars $ fromJust $ ident "polv"

tst_bindLVarToVList
  = testGroup "lookupBind after bindLVarToVListVarToVar"
      [ testCase "polv -> [gpov] (Ok)"
        ( ( llBindLook polv [gpov] ) @?= [gpov] )
      ]


-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nBinding (in Matching)"
      [ tst_bindVarToVar
      , tst_bindVarToTerm
      , tst_bindLVarToVList
      ]
    , testGroup "\nMatching"
      [ testCase "1+1=2" (1+1 @?= 2)
      ]
    ]
