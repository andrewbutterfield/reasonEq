module MatchingTest ( tst_Matching )
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import Data.Set as S

import Test.HUnit
import Test.Framework as TF (testGroup, Test)
--import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import LexBase
import AST
import VarData
import Binding
import Matching

-- -----------------------------------------------------------------------------
tst_match :: TF.Test

k42 = EVal ArbType $ Integer 42

tst_match =
  testGroup "match"
      [ testCase "42 :: 42 (OK)"
        (match [] k42 k42 @?= [emptyBinding] )
      ]

-- -----------------------------------------------------------------------------
tst_tsMatch :: TF.Test

k58 = EVal ArbType $ Integer 58

lst = fromJust $ ident "lst" ; list ts = Cons P lst ts

l_42    = list [k42]
l_42_58 = list [k42,k58]
l_58_42 = list [k58,k42]

tst_tsMatch =
  testGroup "tsMatch (via match)"
      [ testCase "[42,58] :: [42,58] (OK)"
        (match [] l_42_58 l_42_58 @?= [emptyBinding] )
      , testCase "[42] :: [42,58] (FAIL)"
        (match [] l_42 l_42_58 @?= [] )
      , testCase "[42,58] :: [42] (FAIL)"
        (match [] l_42_58 l_42 @?= [] )
      , testCase "[42,58] :: [42] (FAIL)"
        (match [] l_42_58 l_58_42 @?= [] )
      ]

-- -----------------------------------------------------------------------------
tst_vMatch, tst_vMatchVm :: TF.Test

x = PreVar $ fromJust $ ident "x"
xk = E ArbType
y = PreVar $ fromJust $ ident "y"
ex = EVar ArbType x
ey = EVar ArbType y


tst_vMatchVm =
  testGroup "vMatch (via match)"
      [ testCase "42 :: V x (OK)"
        ( (match [] k42 ex :: [Binding] )
          @?= bindVarToTerm x k42 emptyBinding )
      , testCase "V y :: V x (OK)"
        ( (match [] ey ex :: [Binding] )
          @?= bindVarToTerm x ey emptyBinding )
      ]

b0  = S.empty
bx = S.singleton $ StdVar x
by = S.singleton $ StdVar y
ok = PreVar $ fromJust $ ident "ok"
bool = GivenType $ fromJust $ ident "B"
okk = E bool
eok = EVar bool ok
true = EVal bool $ Boolean True
v42 = Vbl (fromJust $ ident "v42") ObsV Static
v42k = E ArbType
oK = Vbl (fromJust $ ident "oK") ObsV Static
oKk = E ArbType
vt = fromJust $ addKnownVar ok bool
   $ fromJust $ addKnownConst v42 k42
   $ fromJust $ addKnownConst oK eok $ newVarTable


tst_vMatch =
  testGroup "vMatch (direct)"
      [ testCase "V y :: x, both bound (Ok)"
        ( (vMatch [] emptyBinding by bx ey xk x :: [Binding] )
          @?= bindVarToVar x y emptyBinding )
      , testCase "V y :: x, only x bound (FAIL)"
        ( vMatch [] emptyBinding b0 bx ey xk x @?= [] )
      , testCase "V y :: x, only y bound (OK)"
        ( (vMatch [] emptyBinding by b0 ey xk x :: [Binding])
          @?= bindVarToTerm x ey emptyBinding  )
      , testCase "V y :: x, both free (OK)"
        ( (vMatch [] emptyBinding b0 b0 ey xk x :: [Binding])
          @?= bindVarToTerm x ey emptyBinding  )
      , testCase "V ok :: ok, known (Ok)"
        ( (vMatch [vt] emptyBinding b0 b0 eok okk ok :: [Binding] )
          @?= bindVarToVar ok ok emptyBinding )
      , testCase "42 :: v42, known (Ok)"
        ( (vMatch [vt] emptyBinding b0 b0 k42 v42k v42 :: [Binding] )
          @?= bindVarToTerm v42 k42 emptyBinding )
      , testCase "58 :: v42, known (FAIL)"
        ( vMatch [vt] emptyBinding b0 b0 k58 v42k v42 @?= [] )
      , testCase "V ok :: oK, known (Ok)"
        ( (vMatch [vt] emptyBinding b0 b0 eok oKk oK :: [Binding] )
          @?= bindVarToVar oK ok emptyBinding )
      , testCase "true :: ok, known (Ok)"
        ( (vMatch [vt] emptyBinding b0 b0 true okk ok :: [Binding] )
          @?= bindVarToTerm ok true emptyBinding )
      ]

-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nMatching  (candidate :: pattern)"
      [ tst_match
      , tst_tsMatch
      , tst_vMatchVm
      , tst_vMatch
      ]
    ]
