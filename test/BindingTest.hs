module BindingTest ( tst_Binding )
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import Data.Set as S (singleton)

import Test.HUnit
import Test.Framework as TF (testGroup, Test)
--import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import LexBase
import AST
import VarData
import Binding

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

gcov = StdVar cov
gcev = StdVar pev
gcpv = StdVar ppv

polv = PreVars $ fromJust $ ident "polv"
pelv = PreExprs $ fromJust $ ident "pelv"
pplv = PrePreds $ fromJust $ ident "pplv"

tst_bindLVarToVList
 = testGroup "lookupBind after bindLVarToVList"
  [ testCase "polv -> [gcov] (Ok)" (llBindLook polv [gcov] @?= BindList [gcov])
  , testCase "polv -> [gcev] (Ok)" (llBindLook polv [gcev] @?= BindList [gcev])
  , testCase "pelv -> [gcev] (Ok)" (llBindLook pelv [gcev] @?= BindList [gcev])
  , testCase "pplv -> [gcpv] (Ok)" (llBindLook pplv [gcpv] @?= BindList [gcpv])
  , testCase "polv -> [gcpv] (Nok)"
    ( bindLVarToVList polv [gcpv] emptyBinding @?= Nothing )
  , testCase "pelv -> [gcov] (Nok)"
    ( bindLVarToVList pelv [gcov] emptyBinding @?= Nothing )
  , testCase "pelv -> [gcpv] (Nok)"
    ( bindLVarToVList pelv [gcpv] emptyBinding @?= Nothing )
  , testCase "pplv -> [gcov] (Nok)"
    ( bindLVarToVList pplv [gcov] emptyBinding @?= Nothing )
  , testCase "pplv -> [gcev] (Nok)"
    ( bindLVarToVList pplv [gcev] emptyBinding @?= Nothing )
  ]

-- -----------------------------------------------------------------------------
tst_bindLVarToVSet :: TF.Test
lsBindLook = bindLook lookupLstBind bindLVarToVSet

sngl = S.singleton

tst_bindLVarToVSet
 = testGroup "lookupBind after bindLVarToVSet"
  [ testCase "polv -> [gcov] (Ok)" (lsBindLook polv (sngl gcov) @?= BindSet (sngl gcov))
  , testCase "polv -> [gcev] (Ok)" (lsBindLook polv (sngl gcev) @?= BindSet (sngl gcev))
  , testCase "pelv -> [gcev] (Ok)" (lsBindLook pelv (sngl gcev) @?= BindSet (sngl gcev))
  , testCase "pplv -> [gcpv] (Ok)" (lsBindLook pplv (sngl gcpv) @?= BindSet (sngl gcpv))
  , testCase "polv -> [gcpv] (Nok)"
    ( bindLVarToVSet polv (sngl gcpv) emptyBinding @?= Nothing )
  , testCase "pelv -> [gcov] (Nok)"
    ( bindLVarToVSet pelv (sngl gcov) emptyBinding @?= Nothing )
  , testCase "pelv -> [gcpv] (Nok)"
    ( bindLVarToVSet pelv (sngl gcpv) emptyBinding @?= Nothing )
  , testCase "pplv -> [gcov] (Nok)"
    ( bindLVarToVSet pplv (sngl gcov) emptyBinding @?= Nothing )
  , testCase "pplv -> [gcev] (Nok)"
    ( bindLVarToVSet pplv (sngl gcev) emptyBinding @?= Nothing )
  ]


-- -----------------------------------------------------------------------------
tst_Binding :: [TF.Test]

tst_Binding
  = [ testGroup "\nBinding"
      [ tst_bindVarToVar
      , tst_bindVarToTerm
      , tst_bindLVarToVList
      , tst_bindLVarToVSet
      ]
    ]
