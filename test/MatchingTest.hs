module MatchingTest ( tst_Matching )
where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub)

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
ex = fromJust $ eVar ArbType x
ey = fromJust $ eVar ArbType y


tst_vMatchVm =
  testGroup "tvMatch (via match)"
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
eok = fromJust $ eVar bool ok
true = EVal bool $ Boolean True
v42 = Vbl (fromJust $ ident "v42") ObsV Static
v42k = E ArbType
oK = Vbl (fromJust $ ident "oK") ObsV Static
oKk = E ArbType
vt = fromJust $ addKnownVar ok bool
   $ fromJust $ addKnownConst v42 k42
   $ fromJust $ addKnownConst oK eok $ newVarTable


tst_vMatch =
  testGroup "tvMatch (direct)"
      [ testCase "V y :: x, both bound (Ok)"
        ( (tvMatch [] emptyBinding by bx ey xk x :: [Binding] )
          @?= bindVarToVar x y emptyBinding )
      , testCase "V y :: x, only x bound (FAIL)"
        ( tvMatch [] emptyBinding b0 bx ey xk x @?= [] )
      , testCase "V y :: x, only y bound (OK)"
        ( (tvMatch [] emptyBinding by b0 ey xk x :: [Binding])
          @?= bindVarToTerm x ey emptyBinding  )
      , testCase "V y :: x, both free (OK)"
        ( (tvMatch [] emptyBinding b0 b0 ey xk x :: [Binding])
          @?= bindVarToTerm x ey emptyBinding  )
      , testCase "V ok :: ok, known (Ok)"
        ( (tvMatch [vt] emptyBinding b0 b0 eok okk ok :: [Binding] )
          @?= bindVarToVar ok ok emptyBinding )
      , testCase "42 :: v42, known (Ok)"
        ( (tvMatch [vt] emptyBinding b0 b0 k42 v42k v42 :: [Binding] )
          @?= bindVarToTerm v42 k42 emptyBinding )
      , testCase "58 :: v42, known (FAIL)"
        ( tvMatch [vt] emptyBinding b0 b0 k58 v42k v42 @?= [] )
      , testCase "V ok :: oK, known (Ok)"
        ( (tvMatch [vt] emptyBinding b0 b0 eok oKk oK :: [Binding] )
          @?= bindVarToVar oK ok emptyBinding )
      , testCase "true :: ok, known (Ok)"
        ( (tvMatch [vt] emptyBinding b0 b0 true okk ok :: [Binding] )
          @?= bindVarToTerm ok true emptyBinding )
      ]

-- -----------------------------------------------------------------------------
tst_vlMatch :: TF.Test

-- builders
identi nm i = fromJust $ ident (nm++show i)
mkPS i = StdVar $ PreVar  $ identi "ps" i
mkPL i = LstVar $ PreVars $ identi "pl" i
mkCS i = StdVar $ PreVar  $ identi "cs" i
mkCL i = LstVar $ PreVars $ identi "cl" i
bindVV (StdVar pv)  (StdVar cv)   =  fromJust . bindVarToVar pv cv
bindLL (LstVar plv) cgv  =  fromJust . bindLVarToVList plv [cgv]

[ps1,ps2,ps3,ps4] = map mkPS [1..4]  -- std pattern vars
[pl1,pl2,pl3,pl4] = map mkPL [1..4]  -- lst pattern vars
[cs1,cs2,cs3,cs4] = map mkCS [1..4]  -- std candidate vars
[cl1,cl2,cl3,cl4] = map mkCL [1..4]  -- lst candidate vars

bindPSi2CSi :: Binding
bindPSi2CSi
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4 emptyBinding
bindPLi2CLi
 = bindLL pl1 cl1 $ bindLL pl2 cl2 $ bindLL pl3 cl3 $ bindLL pl4 cl4 emptyBinding
bindAll
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4
 $ bindLL pl1 cl1 $ bindLL pl2 cl2 $ bindLL pl3 cl3 $ bindLL pl4 cl4 emptyBinding

tst_vlMatch =
  testGroup "vlMatch"
    [ testCase "[] :: [] (OK)"
      ( vlMatch [] emptyBinding b0 b0 [] [] @?= [emptyBinding]  )
    , testCase "[] :: [ps1] (FAIL)"
      ( vlMatch [] emptyBinding b0 b0 [] [ps1] @?= []  )
    , testCase "[cs1] :: [] (FAIL)"
      ( vlMatch [] emptyBinding b0 b0 [cs1] [] @?= []  )
    , testCase "[cs1] :: [ps1] (OK)"
      ( (vlMatch [] emptyBinding b0 b0 [cs1] [ps1] ::[Binding])
        @?= bindGVarToVList ps1 [cs1] emptyBinding  )
    , testCase "[cs2] :: [ps1] where ps1 |-> cs1 (FAIL)"
      ( vlMatch [] bindPSi2CSi b0 b0 [cs2] [ps1] @?= [] )
    , testCase "[cs2,cs1] :: [ps1,ps2] where ps_i |-> cs+i (FAIL)"
      ( vlMatch [] bindPSi2CSi b0 b0 [cs2,cs1] [ps1,ps2] @?= [] )
    , testCase "[cs_i,cl_i] :: [ps_i,pl_i], no pre-bind  (OK)"
      ( nub ( vlMatch [] emptyBinding b0 b0
               [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4]
               [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )
        @?= [bindAll] )
    , testCase "[cl_i,cs_i] :: [pl_i,ps_i], no pre-bind  (OK)"
      ( nub ( vlMatch [] emptyBinding b0 b0
                 [cl1,cs1,cl2,cs2,cl3,cs3,cl4,cs4]
                 [pl1,ps1,pl2,ps2,pl3,ps3,pl4,ps4] )
        @?= [bindAll] )
    , testCase "[cs_i,cl_i] :: [ps_i,pl_i], ps_i |-> cs_i  (OK)"
      ( (nub ( vlMatch [] bindPSi2CSi b0 b0
               [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4]
               [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )) !! 9
        -- 19 bindings possible, with vlFreeMatchN where N=2
        -- 10th one returned is our bindAll
        @?= bindAll )
    , testCase "[cs_i,cl_i] :: [ps_i,pl_i], pl_i |-> [cl_i]  (OK)"
      ( nub ( vlMatch [] bindPLi2CLi b0 b0
               [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4]
               [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )
        @?= [bindAll] )
    ]

-- -----------------------------------------------------------------------------
tst_vsMatch :: TF.Test

tst_vsMatch =
  testGroup "vsMatch"
    [ testCase "{} :: {} (OK)"
      ( vsMatch [] emptyBinding b0 b0 S.empty S.empty @?= [emptyBinding]  )
    , testCase "{} :: {ps1} (FAIL)"
      ( vsMatch [] emptyBinding b0 b0 S.empty (S.fromList [ps1]) @?= []  )
    , testCase "{cs1} :: {} (FAIL)"
      ( vsMatch [] emptyBinding b0 b0 (S.fromList [cs1]) S.empty @?= []  )
    , testCase "{cs1} :: {ps1} (OK)"
      ( (vsMatch [] emptyBinding b0 b0 (S.fromList [cs1]) (S.fromList [ps1])
          ::[Binding])
        @?= bindGVarToVList ps1 [cs1] emptyBinding  )
    -- , testCase "[cs2] :: [ps1] where ps1 |-> cs1 (FAIL)"
    --   ( vlMatch [] bindPSi2CSi b0 b0 [cs2] [ps1] @?= [] )
    -- , testCase "[cs2,cs1] :: [ps1,ps2] where ps_i |-> cs+i (FAIL)"
    --   ( vlMatch [] bindPSi2CSi b0 b0 [cs2,cs1] [ps1,ps2] @?= [] )
    -- , testCase "[cs_i,cl_i] :: [ps_i,pl_i], no pre-bind  (OK)"
    --   ( nub ( vlMatch [] emptyBinding b0 b0
    --            [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4]
    --            [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )
    --     @?= [bindAll] )
    -- , testCase "[cl_i,cs_i] :: [pl_i,ps_i], no pre-bind  (OK)"
    --   ( nub ( vlMatch [] emptyBinding b0 b0
    --              [cl1,cs1,cl2,cs2,cl3,cs3,cl4,cs4]
    --              [pl1,ps1,pl2,ps2,pl3,ps3,pl4,ps4] )
    --     @?= [bindAll] )
    -- , testCase "[cs_i,cl_i] :: [ps_i,pl_i], ps_i |-> cs_i  (OK)"
    --   ( (nub ( vlMatch [] bindPSi2CSi b0 b0
    --            [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4]
    --            [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )) !! 9
    --     -- 19 bindings possible, with vlFreeMatchN where N=2
    --     -- 10th one returned is our bindAll
    --     @?= bindAll )
    -- , testCase "[cs_i,cl_i] :: [ps_i,pl_i], pl_i |-> [cl_i]  (OK)"
    --   ( nub ( vlMatch [] bindPLi2CLi b0 b0
    --            [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4]
    --            [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )
    --     @?= [bindAll] )
    ]

-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nMatching  (candidate :: pattern)"
      [ tst_match
      , tst_tsMatch
      , tst_vMatchVm
      , tst_vMatch
      , tst_vlMatch
      , tst_vsMatch
      ]
    ]
