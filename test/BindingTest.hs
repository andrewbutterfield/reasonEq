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
      , testCase "ob_v -> ob_u, lkp(odm_v) (Not Ok)"
        ( lookupBind (fromJust $ bindVarToVar ob_v ob_u emptyBinding) odm_v
           @?= Nothing )
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

obu = ObsVar  (fromJust $ ident "obu") Before
ebv = ExprVar (fromJust $ ident "ebv") Before
pbv = PredVar (fromJust $ ident "pbv") Before

gosu = StdVar osu
gesv = StdVar esv
gpsv = StdVar psv

gobu = StdVar obu
gebv = StdVar ebv
gpbv = StdVar pbv

lobv = PreVars $ fromJust $ ident "lobv"
lebv = PreExprs $ fromJust $ ident "lebv"
lpbv = PrePreds $ fromJust $ ident "lpbv"

tst_bind_lkp_LVarToVList
 = testGroup "lookupBind after bindLVarToVList"
  [ testCase "lobv -> [gobu] (Ok)" (llBindLook lobv [gobu] @?= BindList [gobu])
  , testCase "lobv -> [gebv] (Ok)" (llBindLook lobv [gebv] @?= BindList [gebv])
  , testCase "lebv -> [gebv] (Ok)" (llBindLook lebv [gebv] @?= BindList [gebv])
  , testCase "lpbv -> [gpbv] (Ok)" (llBindLook lpbv [gpbv] @?= BindList [gpbv])
  , testCase "lobv -> [gpsv] (Nok)"
    ( bindLVarToVList lobv [gpsv] emptyBinding @?= Nothing )
  , testCase "lebv -> [gobu] (Nok)"
    ( bindLVarToVList lebv [gobu] emptyBinding @?= Nothing )
  , testCase "lebv -> [gpbv] (Nok)"
    ( bindLVarToVList lebv [gpbv] emptyBinding @?= Nothing )
  , testCase "lpbv -> [gosu] (Nok)"
    ( bindLVarToVList lpbv [gobu] emptyBinding @?= Nothing )
  , testCase "lpbv -> [gesv] (Nok)"
    ( bindLVarToVList lpbv [gebv] emptyBinding @?= Nothing )
  ]

-- -----------------------------------------------------------------------------
tst_bind_lkp_LVarToVSet :: TF.Test
lsBindLook = bindLook lookupLstBind bindLVarToVSet

sngl = S.singleton

tst_bind_lkp_LVarToVSet
 = testGroup "lookupBind after bindLVarToVSet"
  [ testCase "lobv -> {gobu} (Ok)" (lsBindLook lobv (sngl gobu) @?= BindSet (sngl gobu))
  , testCase "lobv -> {gebv} (Ok)" (lsBindLook lobv (sngl gebv) @?= BindSet (sngl gebv))
  , testCase "lebv -> {gebv} (Ok)" (lsBindLook lebv (sngl gebv) @?= BindSet (sngl gebv))
  , testCase "lpbv -> {gpbv} (Ok)" (lsBindLook lpbv (sngl gpbv) @?= BindSet (sngl gpbv))
  , testCase "lobv -> {gpsv} (Nok)"
    ( bindLVarToVSet lobv (sngl gpsv) emptyBinding @?= Nothing )
  , testCase "lebv -> {gobu} (Nok)"
    ( bindLVarToVSet lebv (sngl gobu) emptyBinding @?= Nothing )
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
