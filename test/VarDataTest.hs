module VarDataTest ( tst_VarData )
{-
Copyright  Andrew Buttefield (c) 2017-18

LICENSE: BSD3, see file LICENSE at reasonEq root
-}
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList, lookup, empty)
import Data.Set as S (fromList, singleton, empty)

import Test.HUnit
--import Test.Framework as TF (testGroup, Test)
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Utilities
import LexBase
import Variables
import AST
import VarData
import TestRendering

--import TestDefs

sngl = S.singleton

i = ObsVar  (jId "i") Static; ti = fromJust $ eVar ArbType i
j = ObsVar  (jId "j") Static; tj = fromJust $ eVar ArbType j
k = ObsVar  (jId "k") Static; tk = fromJust $ eVar ArbType k
u = ObsVar  (jId "u") Before; tu = fromJust $ eVar ArbType u
v = ObsVar  (jId "v") Before; tv = fromJust $ eVar ArbType v
v' = ObsVar  (jId "v") Before; tv' = fromJust $ eVar ArbType v'
e = ExprVar (jId "e") Before; te = fromJust $ eVar ArbType e
len = ExprVar (jId "len") Static; tlen = fromJust $ eVar ArbType len
p = PredVar (jId "P") Before; tp = fromJust $ pVar p
pT = PredVar (jId "T") Static; tT = fromJust $ pVar pT

iu = jId "lu" ; lu = PreVars  iu ; glu  = LstVar lu
iv = jId "lv" ; lv = PreVars  iv ; glv  = LstVar lv
lw  = PreVars  $ jId "lw"     ; glw  = LstVar lw
lv' = PostVars $ jId "lv"     ; glv' = LstVar lv'
lvm = MidVars  (jId "lv") "m" ; glvm = LstVar lvm
le  = PreExprs $ jId "le"     ; gle  = LstVar le
lP  = PrePreds $ jId "lP"     ; glP  = LstVar lP

x = ObsVar (jId "x") Static; lx = LVbl x [] []; glx = LstVar lx
ll  = PreVars  $ jId "ll"     ; gll  = LstVar ll
ls  = PreVars  $ jId "ls"     ; gls  = LstVar ls
f = ExprVar (jId "f") Static ; lf = LVbl f [] []

gi = StdVar i; gj = StdVar j
gv = StdVar v; ge = StdVar e; gp = StdVar p

aKC v t    =  fromJust . addKnownConst   v  t
aKV v t    =  fromJust . addKnownVar     v  t
aKL lv vl  =  fromJust . addKnownVarList (varOf lv) vl
aKS lv vs  =  fromJust . addKnownVarSet  (varOf lv) vs

vlu = varOf lu

tst_vardata_inserts -- not run as standard regression
-- because some tests are meant to fail
 = testGroup "Check VarData insertion shorthands"
     [ testCase "aKC: i ^= j  fails"
         ( vtList (aKC i tj newVarTable)
           @?= [(i,KnownConst tj)] )
     , testCase "aKV: i : tau succeeds"
         ( vtList (aKV i ArbType newVarTable)
           @?= [(i,KnownVar ArbType)] )
     , testCase "aKC.aKV: i : tau, then j ^=i succeeds"
         ( vtList (aKC j ti $ aKV i ArbType newVarTable)
           @?= [(i,KnownVar ArbType),(j,KnownConst ti)] )
     , testCase "aKL: lu ^= [glu] fails"
         ( dtList (aKL lu [glu] newVarTable)
           @?= [(vlu,KnownVarList [glu] [] 0)] )
     , testCase "aKL: lu ^= [gi] fails"
         ( dtList (aKL lu [gi] newVarTable)
           @?= [(vlu,KnownVarList [gi] [] 0)] )
     , testCase "aKL: lu ^= [gv] fails"
         ( dtList (aKL lu [gv] newVarTable)
           @?= [(vlu,KnownVarList [gv] [] 0)] )
     , testCase "aKL.aKV: i : tau, then lu ^= [gi] fails"
         ( dtList (aKL lu [gi] $ aKV i ArbType newVarTable)
           @?= [(vlu,KnownVarList [gi] [] 0)] )
     , testCase "dtList.aKL.aKV: v : tau, then lu ^= [gv] succeeds"
         ( dtList (aKL lu [gv] $ aKV v ArbType newVarTable)
           @?= [(vlu,KnownVarList [gv] [] 0)] )
     , testCase "vtList.aKL.aKV: v : tau, then lu ^= [gv] succeeds"
         ( vtList (aKL lu [gv] $ aKV v ArbType newVarTable)
           @?= [(v,KnownVar ArbType)] )
     , testCase "aKV.aKV: i : tau, then v : tau succeeds"
         ( vtList (aKV v ArbType $ aKV i ArbType newVarTable)
           @?= [(i,KnownVar ArbType),(v,KnownVar ArbType)] )
     , testCase "aKL.aKV.aKV: i : tau, then v : tau, then lu ^= [gv,gi] fails"
         ( vtList (aKL lu [gv,gi] $ aKV v ArbType $ aKV i ArbType newVarTable)
           @?= [(v,KnownVar ArbType)] )
     ]

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
     , testCase "k |-> 99 after k |-> 42 should fail"
       ( addKnownConst k k99 (fromJust (addKnownConst k k42 newVarTable))
         @?= Nothing )
     ]

-- -----------------------------------------------------------------------------
tst_addKnownVar :: TF.Test

tBool = GivenType $ jId "Bool"
tInt = GivenType $ jId "Int"

tst_addKnownVar
 = testGroup "addKnownVar"
     [ testCase "k : Bool"
       ( vtList (fromJust (addKnownVar k tBool newVarTable))
         @?= [(k,KnownVar tBool)] )
     , testCase "v : Int "
       ( vtList (fromJust (addKnownVar v tInt newVarTable))
         @?= [(v,KnownVar tInt)] )
     , testCase "e : Int "
       ( vtList (fromJust (addKnownVar e tInt newVarTable))
        @?= [(e,KnownVar tInt)] )
     , testCase "T : Bool"
       ( vtList (fromJust (addKnownVar pT tBool newVarTable))
        @?= [(pT,KnownVar tBool)] )
     ]

-- -----------------------------------------------------------------------------
tst_addGenericVar :: TF.Test


tst_addGenericVar
 = testGroup "addGenericVar"
     [ testCase "v into empty table"
       ( vtList (fromJust (addGenericVar v newVarTable))
         @?= [(v,GenericVar)] )
     , testCase "v' into empty table"
       ( vtList (fromJust (addGenericVar v' newVarTable))
         @?= [(v',GenericVar)] )
     , testCase "e into empty table"
       ( vtList (fromJust (addGenericVar e newVarTable))
         @?= [(e,GenericVar)] )
     , testCase "p into empty table"
       ( vtList (fromJust (addGenericVar p newVarTable))
         @?= [(p,GenericVar)] )
     , testCase "v into table with e"
       ( vtList ( fromJust $ addGenericVar v
                $ fromJust (addGenericVar e newVarTable))
         @?= [(e,GenericVar),(v,GenericVar)] )
     , testCase "v into table with v (should fail)"
       ( addGenericVar v (fromJust (addGenericVar v newVarTable))
         @?= Nothing )
     , testCase "v into table with v' (should fail)"
       ( addGenericVar v (fromJust (addGenericVar v' newVarTable))
         @?= Nothing )
     ]

-- -----------------------------------------------------------------------------
tst_addInstanceVar :: TF.Test

gvTable = fromJust $ addGenericVar v newVarTable

tst_addInstanceVar
 = testGroup "addInstanceVar"
     [ testCase "v as v into empty table (fails)"
       ( addInstanceVar v v newVarTable @?= Nothing )
     , testCase "v as v into table with v (fails)"
       ( addInstanceVar v v gvTable @?= Nothing )
     , testCase "v as v' into table with v (fails)"
       ( addInstanceVar v v' gvTable @?= Nothing )
     , testCase "v' as v into table with v (fails)"
       ( addInstanceVar v' v gvTable @?= Nothing )
     , testCase "e as v into table with v (fails)"
       ( addInstanceVar e v gvTable @?= Nothing )
     , testCase "e as v' into table with v (fails)"
       ( addInstanceVar e v' gvTable @?= Nothing )
     , testCase "u as v into empty table (fails)"
       ( addInstanceVar e v' newVarTable @?= Nothing )
     , testCase "u as v into table with v"
       ( vtList (fromJust (addInstanceVar u v gvTable))
         @?= [(u,InstanceVar v),(v,GenericVar)] )
     ]

-- -----------------------------------------------------------------------------
tst_lookupVarTable :: TF.Test

kvepTable
  = fromJust $ addKnownConst pT pTrue
  $ fromJust $ addKnownConst len k99
  $ fromJust $ addKnownVar v tInt
  $ fromJust $ addKnownVar k tBool newVarTable

z = ObsVar (jId "z") Static

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

-- setup vardata where i,j,u,len and T are known
-- and ll and ls map to empty lists and sets respectively
-- and lf maps to [len]
iltVarData
  = aKL lf [StdVar len] $
    aKV i ArbType $ aKV j ArbType $ aKV u ArbType $
    aKV len ArbType $ aKV pT ArbType $
    aKL ll [] $ aKS ls S.empty  newVarTable

vle = varOf le
vlP = varOf lP
vlv = varOf lv
vll = varOf ll
vls = varOf ls
vlf = varOf lf
vlx = varOf lx

tst_addKnownListVar
 = testGroup "addKnownVarList/Set"
     [ -- inconsistent classifications
       testCase "lu |-> <lv'>, inconsistent!"
       ( addKnownVarList vlu [glv'] newVarTable @?= Nothing )
     , testCase "lu |-> <le>, inconsistent!"
       ( addKnownVarList vlu [gle]  newVarTable @?= Nothing )
     , testCase "le |-> <lu>, inconsistent!"
        ( addKnownVarList vle [glu] newVarTable @?= Nothing )
     , testCase "lP |-> <le>, inconsistent!"
        ( addKnownVarList vlP [gle] newVarTable @?= Nothing )
     -- some map to ... the other
     , testCase "lv |-> <ls>, set and list!"
        ( addKnownVarList vlv [gls] iltVarData @?= Nothing )
     , testCase "lv |-> {ll}, set and list - succeeds"
        ( dtList (aKS lv (sngl gll) iltVarData)
          @?= [(vll,KnownVarList [] [] 0)
              ,(vls,KnownVarSet S.empty S.empty 0)
              ,(vlv,KnownVarSet (sngl gll) S.empty 0)] )
     , testCase "lv |-> <ll,ls>, set and list!"
        ( addKnownVarList vlv [gll,gls] iltVarData @?= Nothing )
     -- list-variable cycle
     , testCase "ll |-> <ll>, cycle!"
        ( addKnownVarList vll [gll] iltVarData @?= Nothing )
     , testCase "ls |-> {ls}, cycle!"
        ( addKnownVarSet vls (sngl gls) iltVarData @?= Nothing )
     -- range list contains unknown variables
     , testCase "lv |-> [lw], unknowns!"
        ( addKnownVarList vlv [glw] iltVarData @?= Nothing )
     -- trying to update entry
     , testCase "lf |-> [len,len], update!"
        ( addKnownVarList vlf [StdVar len,StdVar len] iltVarData @?= Nothing )
     -- successful entries
     , testCase "lu |-> [], succeeds"
        ( dtList (aKL lu [] iltVarData)
         @?= [(vll,KnownVarList [] [] 0)
             ,(vls,KnownVarSet S.empty S.empty 0)
             ,(vlu,KnownVarList [] [] 0)] )
     , testCase "lx |-> [], succeeds"
        ( stList (aKL lx [] iltVarData)
         @?= [ (vlf,KnownVarList [StdVar len] [len] 1)
             , (vlx,KnownVarList [] [] 0) ] )
     , testCase "lx |-> [i,j], succeeds"
        ( stList (aKL lx [gi,gj] iltVarData)
         @?= [ (vlf,KnownVarList [StdVar len] [len] 1)
             , (vlx,KnownVarList [gi,gj] [i,j] 2)] )
     , testCase "lx |-> {i,j}, succeeds"
        ( stList (aKS lx (S.fromList [gi,gj]) iltVarData)
         @?= [ (vlf,KnownVarList [StdVar len] [len] 1)
             , (vlx,KnownVarSet (S.fromList [gi,gj]) (S.fromList [i,j]) 2)] )
     ]

lulvTable = fromJust $ addKnownVarList vlu [glv]             newVarTable
lulwTable = fromJust $ addKnownVarSet  vlu (S.singleton glw) newVarTable

tst_lookupLVarTable
 = testGroup "lookupLVarTable"
     [ testCase "lu in empty table, should be UnknownListVar"
       ( lookupLVarTable newVarTable vlu @?= UnknownListVar )
     , testCase "ll in iltVarData, should be []"
       ( lookupLVarTable iltVarData vll @?= KnownVarList [] [] 0)
     , testCase "ls in iltVarData, should be {}"
       ( lookupLVarTable iltVarData vls @?= KnownVarSet S.empty S.empty 0)
     ]



-- -----------------------------------------------------------------------------
tst_VarData :: [TF.Test]
tst_VarData
  = [ testGroup "\nVarData"
      [ tst_addKnownConst
      , tst_addKnownVar
      , tst_addGenericVar
      , tst_addInstanceVar
      , tst_lookupVarTable
      , tst_addKnownListVar
      , tst_lookupLVarTable
      ]
    ]
