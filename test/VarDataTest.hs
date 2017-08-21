module VarDataTest ( tst_VarData )
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

k = StaticVar    $  fromJust $ ident "k"
v = ObsVar  Before (fromJust $ ident "v")
e = ExprVar Before (fromJust $ ident "e")
p = PredVar Before (fromJust $ ident "P")

-- -----------------------------------------------------------------------------
tst_addKnownConst :: TF.Test

k42 = EVal ArbType $ Integer 42
k99 = EVal ArbType $ Integer 99
pTrue = PVal $ Boolean True

tst_addKnownConst
 = testGroup "addKnownConst"
     [ testCase "k known as 42"
       ( vtList (addKnownConst k k42 newVarTable) @?= [(k,KnownConst k42)] )
     , testCase "v known as 99"
       ( vtList (addKnownConst v k99 newVarTable) @?= [(v,KnownConst k99)] )
     , testCase "e known as 99"
       ( vtList (addKnownConst e k99 newVarTable) @?= [(e,KnownConst k99)] )
     , testCase "p known as True"
       ( vtList (addKnownConst p pTrue newVarTable) @?= [(p,KnownConst pTrue)] )
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
     , testCase "p : Bool"
       ( addKnownVar p tBool newVarTable @?= Nothing )
     ]

-- -----------------------------------------------------------------------------
tst_lookupVarTable :: TF.Test

kvepTable
  = addKnownConst p pTrue
  $ addKnownConst e k99
  $ fromJust $ addKnownVar v tInt
  $ fromJust $ addKnownVar k tBool newVarTable

z = ObsVar After $ fromJust $ ident "z"

tst_lookupVarTable
 = testGroup "lookupVarTable"
     [ testCase "k in empty table"
       ( lookupVarTable newVarTable k @?= UnknownVar)
     , testCase "k in complete table"
       ( lookupVarTable kvepTable k @?= KnownVar tBool)
     , testCase "v in empty table"
       ( lookupVarTable newVarTable v @?= UnknownVar)
     , testCase "v in complete table"
       ( lookupVarTable kvepTable v @?= KnownVar tInt)
     , testCase "e in empty table"
       ( lookupVarTable newVarTable e @?= UnknownVar)
     , testCase "e in complete table"
       ( lookupVarTable kvepTable e @?= KnownConst k99)
     , testCase "p in empty table"
       ( lookupVarTable newVarTable p @?= UnknownVar)
     , testCase "p in complete table"
       ( lookupVarTable kvepTable p @?= KnownConst pTrue)
     , testCase "z in complete table"
       ( lookupVarTable kvepTable z @?= UnknownVar )
     ]



-- -----------------------------------------------------------------------------
tst_VarData :: [TF.Test]
tst_VarData
 = [ tst_addKnownConst
   , tst_addKnownVar
   , tst_lookupVarTable
   ]
