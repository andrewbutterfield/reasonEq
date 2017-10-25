module VarDataTest ( tst_VarData )
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
import AST
import VarData

i = ObsVar  (fromJust $ ident "i") Static
j = ObsVar  (fromJust $ ident "j") Static
k = ObsVar  (fromJust $ ident "k") Static
v = ObsVar  (fromJust $ ident "v") (Dynamic Before)
e = ExprVar (fromJust $ ident "e") (Dynamic Before)
len = ExprVar (fromJust $ ident "len") Static
p = PredVar (fromJust $ ident "P") (Dynamic Before)
pT = PredVar (fromJust $ ident "T") Static

-- -----------------------------------------------------------------------------
tst_addKnownConst :: TF.Test

k42 = EVal ArbType $ Integer 42
k99 = EVal ArbType $ Integer 99
pTrue = PVal $ Boolean True
ki = fromJust $ eVar ArbType i
kj = fromJust $ eVar ArbType j
kk = fromJust $ eVar ArbType k

tst_addKnownConst
 = testGroup "addKnownConst"
     [ testCase "k known as 42"
       ( vtList (fromJust (addKnownConst k k42 newVarTable))
         @?= [(k,KnownConst k42)] )
     , testCase "v known as 99"
       ( addKnownConst v k99 newVarTable @?= Nothing )
     , testCase "e known as 99"
       ( addKnownConst e k99 newVarTable @?= Nothing )
     , testCase "len known as 99"
       ( vtList (fromJust (addKnownConst len k99 newVarTable))
         @?= [(len,KnownConst k99)] )
     , testCase "P known as True"
       ( addKnownConst p pTrue newVarTable @?= Nothing )
     , testCase "T known as True"
       ( vtList (fromJust (addKnownConst pT pTrue newVarTable))
         @?= [(pT,KnownConst pTrue)] )
     , testCase "k |-> j should succeed"
       ( vtList (fromJust (addKnownConst k kj newVarTable))
         @?= [(k,KnownConst kj)] )
     , testCase "j |-> k should succeed"
       ( vtList (fromJust (addKnownConst j kk newVarTable))
         @?= [(j,KnownConst kk)] )
     , testCase "i -> j -> k should succeed"
       ( vtList (fromJust (addKnownConst j kk
                (fromJust (addKnownConst i kj newVarTable))))
         @?= [(i,KnownConst kj),(j,KnownConst kk)] )
     , testCase "k -> j -> k should fail"
       ( (addKnownConst j kk
             (fromJust (addKnownConst k kj newVarTable)))
         @?= Nothing )
     , testCase "i -> j -> k -> i should fail"
       ( (addKnownConst k ki
                (fromJust (addKnownConst j kk
                (fromJust (addKnownConst i kj newVarTable)))))
         @?= Nothing )
     ]

-- -----------------------------------------------------------------------------
tst_addKnownVar :: TF.Test

tBool = GivenType $ fromJust $ ident "Bool"
tInt = GivenType $ fromJust $ ident "Int"

tst_addKnownVar
 = testGroup "addKnownVar"
     [ testCase "k : Bool"
       ( vtList (fromJust (addKnownVar k tBool newVarTable))
         @?= [(k,KnownVar tBool)] )
     , testCase "v : Int "
       ( vtList (fromJust (addKnownVar v tInt newVarTable))
         @?= [(v,KnownVar tInt)] )
     , testCase "e : Int "
       ( addKnownVar e tInt newVarTable @?= Nothing )
     , testCase "T : Bool"
       ( addKnownVar pT tBool newVarTable @?= Nothing )
     ]

-- -----------------------------------------------------------------------------
tst_lookupVarTable :: TF.Test

kvepTable
  = fromJust $ addKnownConst pT pTrue
  $ fromJust $ addKnownConst len k99
  $ fromJust $ addKnownVar v tInt
  $ fromJust $ addKnownVar k tBool newVarTable

z = ObsVar (fromJust $ ident "z") Static

tst_lookupVarTable
 = testGroup "lookupVarTable"
     [ testCase "k not in empty table"
       ( lookupVarTable newVarTable k @?= UnknownVar)
     , testCase "k in  complete table"
       ( lookupVarTable kvepTable k @?= KnownVar tBool)
     , testCase "v not in empty table"
       ( lookupVarTable newVarTable v @?= UnknownVar)
     , testCase "v in  complete table"
       ( lookupVarTable kvepTable v @?= KnownVar tInt)
     , testCase "len not in empty table"
       ( lookupVarTable newVarTable e @?= UnknownVar)
     , testCase "len in  complete table"
       ( lookupVarTable kvepTable len @?= KnownConst k99)
     , testCase "T not in empty table"
       ( lookupVarTable newVarTable pT @?= UnknownVar)
     , testCase "T in  complete table"
       ( lookupVarTable kvepTable pT @?= KnownConst pTrue)
     , testCase "z not in complete table"
       ( lookupVarTable kvepTable z @?= UnknownVar )
     ]

-- -----------------------------------------------------------------------------
tst_addKnownListVar :: TF.Test

-- pattern PreVars  i    =  LV (VR (i,VO,(KD WB)),[])
-- pattern PostVars i    =  LV (VR (i,VO,(KD WA)),[])
-- pattern MidVars  i n  =  LV (VR (i,VO,(KD (WD n))),[])
-- pattern ScriptVars i  =  LV (VR (i,VV,(KD WB)),[])
-- pattern PreExprs i    =  LV (VR (i,VE,(KD WB)),[])
-- pattern PrePreds i    =  LV (VR (i,VP,(KD WB)),[])
lu  = PreVars  $ fromJust $ ident "lu"     ; glu  = LstVar lu
lv  = PreVars  $ fromJust $ ident "lv"     ; glv  = LstVar lv
lw  = PreVars  $ fromJust $ ident "lw"     ; glw  = LstVar lw
lv' = PostVars $ fromJust $ ident "lv"     ; glv' = LstVar lv'
lvm = MidVars  (fromJust $ ident "lv") "m" ; glvm = LstVar lvm
le  = PreExprs $ fromJust $ ident "le"     ; gle  = LstVar le
lP  = PrePreds $ fromJust $ ident "lP"     ; glP  = LstVar lP

sngl = S.singleton

tst_addKnownListVar
 = testGroup "addKnownVarList"
     [ testCase "lu |-> <lv>, succeeds"
       ( ltList (fromJust (addKnownVarList lu [glv] newVarTable))
         @?= [(lu,KnownVarList [glv])] )
     , testCase "lu |-> <lv>, lv -> <lw> succeeds"
       ( ltList (fromJust (addKnownVarList lu [glv]
                 (fromJust (addKnownVarList lv [glw] newVarTable))))
         @?= [(lu,KnownVarList [glv]),(lv,KnownVarList [glw])] )
     , testCase "lu |-> <lv>, lv -> <lw>, lw -> <lu> fails"
       ( addKnownVarList lu [glv]
                (fromJust (addKnownVarList lv [glw]
                (fromJust (addKnownVarList lw [glu] newVarTable))))
         @?= Nothing )
     , testCase "lu |-> {lv}, succeeds"
        ( ltList (fromJust (addKnownVarSet lu (sngl glv) newVarTable))
          @?= [(lu,KnownVarSet (sngl glv))] )
     , testCase "lu |-> {lv}, lv -> {lw} succeeds"
        ( ltList (fromJust (addKnownVarSet lu (sngl glv)
                  (fromJust (addKnownVarSet lv (sngl glw) newVarTable))))
          @?= [(lu,KnownVarSet (sngl glv)),(lv,KnownVarSet (sngl glw))] )
     , testCase "lu |-> {lv}, lv -> {lw}, lw -> {lu} fails"
        ( addKnownVarSet lu (sngl glv)
                 (fromJust (addKnownVarSet lv (sngl glw)
                 (fromJust (addKnownVarSet lw (sngl glu) newVarTable))))
          @?= Nothing )
     , testCase "lu |-> {lv}, lv -> {lw} succeeds"
        ( ltList (fromJust (addKnownVarSet lu (sngl glv)
                  (fromJust (addKnownVarSet lv (sngl glw) newVarTable))))
          @?= [(lu,KnownVarSet (sngl glv)),(lv,KnownVarSet (sngl glw))] )
     , testCase "lu |-> {lv}, lv -> <lw> fails"
        ( addKnownVarSet lu (sngl glv)
                  (fromJust (addKnownVarList lv [glw] newVarTable))
          @?= Nothing )
     , testCase "lu |-> <lv>, lv -> {lw} fails"
        ( addKnownVarList lu [glv]
                  (fromJust (addKnownVarSet lv (sngl glw) newVarTable))
          @?= Nothing )
     , testCase "lu |-> <lv'>, succeeds"
       ( ltList (fromJust (addKnownVarList lu [glv'] newVarTable))
         @?= [(lu,KnownVarList [glv'])] )
     , testCase "lu |-> <le>, fails (SHOULD IT?)"
       ( addKnownVarList lu [gle] newVarTable @?= Nothing )
      , testCase "le |-> <lu>, fails (SHOULD IT?)"
        ( addKnownVarList le [glu] newVarTable @?= Nothing )
      , testCase "lP |-> <le>, fails (SHOULD IT?)"
        ( addKnownVarList lP [gle] newVarTable @?= Nothing )
      ]

lulvTable = fromJust $ addKnownVarList lu [glv] newVarTable

tst_lookupLVarTable
 = testGroup "lookupLVarTable"
     [ testCase "lu in empty table, should be AnyVarList"
       ( lookupLVarTable newVarTable lu @?= AnyVarList )
     , testCase "lu in lulvTable, should be AnyVarList"
       ( lookupLVarTable lulvTable lu @?= KnownVarList [glv] )
     ]



-- -----------------------------------------------------------------------------
tst_VarData :: [TF.Test]
tst_VarData
  = [ testGroup "\nVarData"
      [ tst_addKnownConst
      , tst_addKnownVar
      , tst_lookupVarTable
      , tst_addKnownListVar
      , tst_lookupLVarTable
      ]
    ]
