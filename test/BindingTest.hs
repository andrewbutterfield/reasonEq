module BindingTest ( tst_Binding )
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import Data.Set as S (singleton)

import Test.HUnit
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import LexBase
import Variables
import AST
import VarData
import Binding

import TestDefs


-- -----------------------------------------------------------------------------
tst_bind_lkp_VarToVar :: TF.Test

tst_bind_lkp_VarToVar
  = testGroup "lookupVarBind after bindVarToVar"
      [ -- variable class tests
        testCase "osv -> osu (Ok)"
        ( vvBindLook  osv osu @?= BindVar osu )
      , testCase "esv -> osu (Ok)"
        ( vvBindLook esv osu @?= BindVar osu)
      , testCase "psv -> osu (Not Ok)"
        ( bindVarToVar psv osu emptyBinding @?= Nothing)
        -- variable temporality tests
      , testCase "obv -> osu (Not Ok)"
        ( bindVarToVar obv osu emptyBinding @?= Nothing)
      , testCase "osv -> obv (Ok)"
        ( vvBindLook  osv osu @?= BindVar osu)
      , testCase "obv -> oav (Not Ok)"
        ( bindVarToVar obv oav emptyBinding @?= Nothing)
      , testCase "osv -> otv (Not Ok)"
        ( bindVarToVar osv otv emptyBinding @?= Nothing)
      , testCase "oav -> obv (Not Ok)"
        ( bindVarToVar oav obv emptyBinding @?= Nothing)
      , testCase "odmv -> oav (Not Ok)"
        ( bindVarToVar odmv oav emptyBinding @?= Nothing)
      , testCase "oav -> odmv (Not Ok)"
        ( bindVarToVar oav odmv emptyBinding @?= Nothing)
      , testCase "odmv -> odmv (Ok)"
        ( vvBindLook  odmv odmv  @?= BindVar odmv)
      , testCase "odmv -> odnv (Ok)"
        ( vvBindLook  odmv odnv  @?= BindVar odnv)
      , testCase "ob_v -> ob_u, lkp(oa_v)=oa_u (Ok)"
        ( vvBindLook2  ob_v ob_u oa_v @?= BindVar oa_u)
      , testCase "ob_v -> ob_u, lkp(odm_v) (Not Ok)"
        ( lookupVarBind (fromJust $ bindVarToVar ob_v ob_u emptyBinding) odm_v
           @?= Nothing )
      , testCase "odm_v -> odm_v_u, lkp(ob_v)=ob_u (Ok)"
        ( vvBindLook2  odm_v odm_u ob_v @?= BindVar ob_u)
      ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_VarToTerm :: TF.Test

tst_bind_lkp_VarToTerm
  = testGroup "lookupVarBind after bindVarToTerm"
      [ testCase "osv -> 42 (Ok)"
        ( ( let (BindTerm k42') = vtBindLook osv k42 in k42' ) @?= k42 )
      , testCase "osv -> True (Not Ok)"
          ( bindVarToTerm osv pTrue emptyBinding @?= Nothing)
      , testCase "esv -> 42 (Ok)"
        ( ( let (BindTerm k42') = vtBindLook esv k42 in k42' ) @?= k42 )
      , testCase "esv -> True (Not Ok)"
            ( bindVarToTerm esv pTrue emptyBinding @?= Nothing)
      , testCase "psv -> 42 (Not Ok)"
        ( bindVarToTerm psv k42 emptyBinding @?= Nothing)
      , testCase "psv -> True (Ok)"
        ( ( let (BindTerm pTrue') = vtBindLook psv pTrue in pTrue' ) @?= pTrue )
      ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_LVarToVList :: TF.Test

tst_bind_lkp_LVarToVList
 = testGroup "lookupVarBind after bindLVarToVList"
  [ testCase "lobv -> [gobu] (Ok)" (llBindLook lobv [gobu] @?= BindList [gobu])
  , testCase "lobv -> [gebv] (Ok)" (llBindLook lobv [gebv] @?= BindList [gebv])
  , testCase "lebv -> [gebv] (Ok)" (llBindLook lebv [gebv] @?= BindList [gebv])
  , testCase "lpbv -> [gpbv] (Ok)" (llBindLook lpbv [gpbv] @?= BindList [gpbv])
  , testCase "lebv -> [gobu] (Ok)" (llBindLook lebv [gobu] @?= BindList [gobu])
  , testCase "lobv -> [gpsv] (Nok)"
    ( bindLVarToVList lobv [gpsv] emptyBinding @?= Nothing )
  , testCase "lebv -> [gpbv] (Nok)"
    ( bindLVarToVList lebv [gpbv] emptyBinding @?= Nothing )
  , testCase "lpbv -> [gosu] (Nok)"
    ( bindLVarToVList lpbv [gobu] emptyBinding @?= Nothing )
  , testCase "lpbv -> [gesv] (Nok)"
    ( bindLVarToVList lpbv [gebv] emptyBinding @?= Nothing )
  ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_LVarToVSet :: TF.Test

tst_bind_lkp_LVarToVSet
 = testGroup "lookupVarBind after bindLVarToVSet"
  [ testCase "lobv -> {gobu} (Ok)" (lsBindLook lobv (sngl gobu) @?= BindSet (sngl gobu))
  , testCase "lobv -> {gebv} (Ok)" (lsBindLook lobv (sngl gebv) @?= BindSet (sngl gebv))
  , testCase "lebv -> {gebv} (Ok)" (lsBindLook lebv (sngl gebv) @?= BindSet (sngl gebv))
  , testCase "lpbv -> {gpbv} (Ok)" (lsBindLook lpbv (sngl gpbv) @?= BindSet (sngl gpbv))
  , testCase "lebv -> {gobu} (Ok)" (lsBindLook lebv (sngl gobu) @?= BindSet (sngl gobu))
  , testCase "lobv -> {gpsv} (Nok)"
    ( bindLVarToVSet lobv (sngl gpsv) emptyBinding @?= Nothing )
  , testCase "lebv -> {gpbv} (Nok)"
    ( bindLVarToVSet lebv (sngl gpbv) emptyBinding @?= Nothing )
  , testCase "lpbv -> {gobu} (Nok)"
    ( bindLVarToVSet lpbv (sngl gobu) emptyBinding @?= Nothing )
  , testCase "lpbv -> {gebv} (Nok)"
    ( bindLVarToVSet lpbv (sngl gebv) emptyBinding @?= Nothing )
  ]


-- -----------------------------------------------------------------------------
tst_Binding :: [TF.Test]

tst_Binding
  = [ testGroup "\nBinding"
      [ tst_bind_lkp_VarToVar
      , tst_bind_lkp_VarToTerm
      , tst_bind_lkp_LVarToVList
      , tst_bind_lkp_LVarToVSet
      ]
    ]

tstBinding = defaultMain tst_Binding
