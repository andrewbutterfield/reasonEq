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

-- ---------------
bindLook lkp bind pv cx
 = fromJust (lkp (fromJust (bind pv cx emptyBinding)) pv)
bindLook2 lkp bind pv1 cx pv2
 = fromJust (lkp (fromJust (bind pv1 cx emptyBinding)) pv2)

-- -----------------------------------------------------------------------------
tst_bind_lkp_VarToVar :: TF.Test
vvBindLook = bindLook lookupBind bindVarToVar
vvBindLook2 = bindLook2 lookupBind bindVarToVar

osv = ObsVar  (fromJust $ ident "osv") Static
osu = ObsVar (fromJust $ ident "osu") Static
esv = ExprVar (fromJust $ ident "esv") Static
psv = PredVar (fromJust $ ident "psv") Static

obv  = ObsVar (fromJust $ ident "obv" )   Before
odmv = ObsVar (fromJust $ ident "odmv") $ During "m"
odnv = ObsVar (fromJust $ ident "odnv") $ During "n"
oav  = ObsVar (fromJust $ ident "oav" )   After
otv  = ObsVar (fromJust $ ident "otv" )   Textual

u = fromJust $ ident "u"
ob_u = ObsVar u Before; oa_u = ObsVar u After; odm_u = ObsVar u $ During "m"
v = fromJust $ ident "v"
ob_v = ObsVar v Before; oa_v = ObsVar v After; odm_v = ObsVar v $ During "m"

tst_bind_lkp_VarToVar
  = testGroup "lookupBind after bindVarToVar"
      [ -- variable class tests
        testCase "osv -> osu (Ok)"
        ( vvBindLook  osv osu @?= BindVar osu )
      , testCase "esv -> osu (Not Ok)"
        ( bindVarToVar esv osu emptyBinding @?= Nothing)
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
      , testCase "ob_v -> ob_u, lkp(odm_v)=odm_u (Ok)"
        ( vvBindLook2  ob_v ob_u odm_v @?= BindVar odm_u)
      , testCase "odm_v -> odm_v_u, lkp(ob_v)=ob_u (Ok)"
        ( vvBindLook2  odm_v odm_u ob_v @?= BindVar ob_u)
      ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_VarToTerm :: TF.Test
vtBindLook = bindLook lookupBind bindVarToTerm

ce42 = EVal ArbType $ Integer 42
pTrue = PVal $ Boolean True

tst_bind_lkp_VarToTerm
  = testGroup "lookupBind after bindVarToTerm"
      [ testCase "osv -> 42 (Ok)"
        ( ( let (BindTerm ce42') = vtBindLook osv ce42 in ce42' ) @?= ce42 )
      , testCase "osv -> True (Not Ok)"
          ( bindVarToTerm osv pTrue emptyBinding @?= Nothing)
      , testCase "esv -> 42 (Ok)"
        ( ( let (BindTerm ce42') = vtBindLook esv ce42 in ce42' ) @?= ce42 )
      , testCase "esv -> True (Not Ok)"
            ( bindVarToTerm esv pTrue emptyBinding @?= Nothing)
      , testCase "psv -> 42 (Not Ok)"
        ( bindVarToTerm psv ce42 emptyBinding @?= Nothing)
      , testCase "psv -> True (Ok)"
        ( ( let (BindTerm pTrue') = vtBindLook psv pTrue in pTrue' ) @?= pTrue )
      ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_LVarToVList :: TF.Test
llBindLook = bindLook lookupLstBind bindLVarToVList

gosu = StdVar osu
gesv = StdVar esv
gpsv = StdVar psv

lobv = PreVars $ fromJust $ ident "lobv"
lebv = PreExprs $ fromJust $ ident "lebv"
lpbv = PrePreds $ fromJust $ ident "lpbv"

tst_bind_lkp_LVarToVList
 = testGroup "lookupBind after bindLVarToVList"
  [ testCase "lobv -> [gosu] (Ok)" (llBindLook lobv [gosu] @?= BindList [gosu])
  , testCase "lobv -> [gesv] (Ok)" (llBindLook lobv [gesv] @?= BindList [gesv])
  , testCase "lebv -> [gesv] (Ok)" (llBindLook lebv [gesv] @?= BindList [gesv])
  , testCase "lpbv -> [gpsv] (Ok)" (llBindLook lpbv [gpsv] @?= BindList [gpsv])
  , testCase "lobv -> [gpsv] (Nok)"
    ( bindLVarToVList lobv [gpsv] emptyBinding @?= Nothing )
  , testCase "lebv -> [gosu] (Nok)"
    ( bindLVarToVList lebv [gosu] emptyBinding @?= Nothing )
  , testCase "lebv -> [gpsv] (Nok)"
    ( bindLVarToVList lebv [gpsv] emptyBinding @?= Nothing )
  , testCase "lpbv -> [gosu] (Nok)"
    ( bindLVarToVList lpbv [gosu] emptyBinding @?= Nothing )
  , testCase "lpbv -> [gesv] (Nok)"
    ( bindLVarToVList lpbv [gesv] emptyBinding @?= Nothing )
  ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_LVarToVSet :: TF.Test
lsBindLook = bindLook lookupLstBind bindLVarToVSet

sngl = S.singleton

tst_bind_lkp_LVarToVSet
 = testGroup "lookupBind after bindLVarToVSet"
  [ testCase "lobv -> {gosu} (Ok)" (lsBindLook lobv (sngl gosu) @?= BindSet (sngl gosu))
  , testCase "lobv -> {gesv} (Ok)" (lsBindLook lobv (sngl gesv) @?= BindSet (sngl gesv))
  , testCase "lebv -> {gesv} (Ok)" (lsBindLook lebv (sngl gesv) @?= BindSet (sngl gesv))
  , testCase "lpbv -> {gpsv} (Ok)" (lsBindLook lpbv (sngl gpsv) @?= BindSet (sngl gpsv))
  , testCase "lobv -> {gpsv} (Nok)"
    ( bindLVarToVSet lobv (sngl gpsv) emptyBinding @?= Nothing )
  , testCase "lebv -> {gosu} (Nok)"
    ( bindLVarToVSet lebv (sngl gosu) emptyBinding @?= Nothing )
  , testCase "lebv -> {gpsv} (Nok)"
    ( bindLVarToVSet lebv (sngl gpsv) emptyBinding @?= Nothing )
  , testCase "lpbv -> {gosu} (Nok)"
    ( bindLVarToVSet lpbv (sngl gosu) emptyBinding @?= Nothing )
  , testCase "lpbv -> {gesv} (Nok)"
    ( bindLVarToVSet lpbv (sngl gesv) emptyBinding @?= Nothing )
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
