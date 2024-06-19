module MatchingTest ( tst_Matching )
where

import Data.Maybe (fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub)

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Utilities
import LexBase
import Variables
import AST
import VarData
import Binding
import Matching

import TestRendering
import TestDefs

-- -----------------------------------------------------------------------------
tst_match :: TF.Test


tst_match =
  testGroup "match"
      [ testCase "42 :: 42 (OK)"
        (match [] k42 k42 @?= [emptyBinding] )
      ]

-- -----------------------------------------------------------------------------
tst_tsMatch, tst_collMatch :: TF.Test

-- we consider first a known list collection type, "lst"
lst = jId "lst" ; v_lst = Vbl lst ExprV Static
lstKnown =  fromJust $ addKnownVar v_lst ArbType $ newVarTable
list ts = Cons ArbType True lst ts

l_42    = list [k42]
l_42_58 = list [k42,k58]
l_58_42 = list [k58,k42]

lst2lst = fromJust $ bindVarToVar v_lst v_lst emptyBinding

tst_tsMatch =
  testGroup "tsMatch list vs. list (via match)"
      [ testCase "[42,58] :: [42,58] (OK)"
        (match [lstKnown] l_42_58 l_42_58 @?= [lst2lst] )
      , testCase "[42] :: [42,58] (FAIL)"
        (match [lstKnown] l_42 l_42_58 @?= [] )
      , testCase "[42,58] :: [42] (FAIL)"
        (match [lstKnown] l_42_58 l_42 @?= [] )
      , testCase "[42,58] :: [58,42] (FAIL)"
        (match [lstKnown] l_42_58 l_58_42 @?= [] )
      ]

-- we now consider matching a generic collection pattern

coll = jId "coll" ; v_coll = Vbl coll ExprV Static
gcoll ts = Cons ArbType True coll ts

c_42_58 = gcoll [k42,k58]

coll2coll = fromJust $ bindVarToVar v_coll v_coll emptyBinding
lst2coll  = fromJust $ bindVarToVar v_coll v_lst emptyBinding

tst_collMatch =
  testGroup "tsMatch known vs. generic (via match)"
      [ testCase "<<42,58>> :: <<42,58>> (OK)"
        (match [lstKnown] c_42_58 c_42_58 @?= [coll2coll] )
      , testCase "[42,58] :: <<42,58>> (OK)"
        (match [lstKnown] l_42_58 c_42_58 @?= [lst2coll] )
      , testCase "<<42,58>> :: [42,58] (FAIL)"
        (match [lstKnown] c_42_58 l_42_58 @?= [] )
      ]


-- -----------------------------------------------------------------------------
tst_tvMatch, tst_vMatchVm, tst_vMatchGI :: TF.Test



tst_vMatchVm =
  testGroup "tvMatch (via match)"
      [ testCase "42 :: V x (OK)"
        ( (match [] k42 ex :: [Binding] )
          @?= bindVarToTerm x k42 emptyBinding )
      , testCase "V y :: V x (OK)"
        ( (match [] ey ex :: [Binding] )
          @?= bindVarToTerm x ey emptyBinding )
      ]

vt = fromJust $ addKnownConst v42 k42
   $ fromJust $ addKnownConst oK eok
   $ fromJust $ addKnownVar ok bool
   $ newVarTable


tst_tvMatch =
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
        ( (tvMatch [vt] emptyBinding b0 b0 pTrue okk ok :: [Binding] )
          @?= bindVarToTerm ok pTrue emptyBinding )
      , testCase "true :: g1, known (Ok)"
        ( (tvMatch [vt] emptyBinding b0 b0 pTrue okk ok :: [Binding] )
          @?= bindVarToTerm ok pTrue emptyBinding )
      ]


gvt = fromJust $ addInstanceVar i12 g1
    $ fromJust $ addInstanceVar i2 g2
    $ fromJust $ addGenericVar g2
    $ fromJust $ addInstanceVar i11 g1
    $ fromJust $ addGenericVar g1
    $ newVarTable

tst_vMatchGI =
  testGroup "vMatch (generic,instances), also some tvMatch"
    [ testCase "g1 :: g1"
      ( (vMatch [gvt] emptyBinding b0 b0 g1 g1 :: [Binding])
        @?= bindVarToVar g1 g1 emptyBinding )
    , testCase "g1 :: g2 (FAIL)"
      ( vMatch [gvt] emptyBinding b0 b0 g1 g2 @?= [] )
    , testCase "i11 :: i11"
      ( (vMatch [gvt] emptyBinding b0 b0 i11 i11 :: [Binding])
        @?= bindVarToVar i11 i11 emptyBinding )
    , testCase "i11 :: g1"
      ( (vMatch [gvt] emptyBinding b0 b0 i11 g1 :: [Binding])
        @?= bindVarToVar g1 i11 emptyBinding )
    , testCase "i12 :: g1"
      ( (vMatch [gvt] emptyBinding b0 b0 i12 g1 :: [Binding])
        @?= bindVarToVar g1 i12 emptyBinding )
    , testCase "i11 :: g2 (FAIL)"
      ( vMatch [gvt] emptyBinding b0 b0 i11 g2 @?= [] )
    , testCase "i3 :: i3"
      ( (vMatch [gvt] emptyBinding b0 b0 i3 i3 :: [Binding])
        @?= bindVarToVar i3 i3 emptyBinding )
    , testCase "i3 :: g2"
      ( vMatch [gvt] emptyBinding b0 b0 i3 g2 @?= [] )
    , testCase "42 :: g1 (FAIL)"
        ( tvMatch [gvt] emptyBinding b0 b0 k42 v42k g1 @?= [] )
    , testCase "42 :: i11 (FAIL)"
        ( tvMatch [gvt] emptyBinding b0 b0 k42 v42k i11 @?= [] )
    ]

-- -----------------------------------------------------------------------------
tst_vlMatch :: TF.Test

-- builders

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
bindSpl2
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4
 $ bindL0 pl1     $ bindLL pl2 cl2 $ bindL0 pl3     $ bindL0 pl4     emptyBinding

tst_vlMatch =
  testGroup "vlMatch"
    [ testCase "[] :: [] (FAIL)"
      ( vlMatch [] emptyBinding b0 b0 [] [] @?= []  )
    , testCase "[] :: [ps1] (FAIL)"
      ( vlMatch [] emptyBinding b0 b0 [] [ps1] @?= []  )
    , testCase "[cs1] :: [] (FAIL)"
      ( vlMatch [] emptyBinding b0 b0 [cs1] [] @?= []  )
    , testCase "[cs1] :: [ps1] (OK)"
      ( (vlMatch [] emptyBinding b0 b0 [cs1] [ps1] ::[Binding])
        @?= bindGVarToVList ps1 [cs1] emptyBinding  )
    , testCase "[cs2] :: [ps1] where ps1 |-> cs1 (FAIL)"
      ( vlMatch [] bindPSi2CSi b0 b0 [cs2] [ps1] @?= [] )
    , testCase "[cs2,cs1] :: [ps1,ps2] where ps_i |-> cs_i (FAIL)"
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
    , testCase "[cs_1,cs_2,cl_2,cs_3,cs_4] :: [ps_i,pl_i], no pre-bind  (OK)"
      ( nub ( vlMatch [] emptyBinding b0 b0
               [cs1,    cs2,cl2,cs3,    cs4]
               [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4] )
        @?= [bindSpl2] )
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

bindPS12CS12
 = bindVV ps1 cs1 $ bindVV ps2 cs2 emptyBinding
bindPSSi2CSSi
 = bindLS pl1 cl1 $ bindLS pl2 cl2 $ bindLS pl3 cl3 $ bindLS pl4 cl4 emptyBinding
bindAllS
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4
 $ bindLS pl1 cl1 $ bindLS pl2 cl2 $ bindLS pl3 cl3 $ bindLS pl4 cl4 emptyBinding
bindAllT
 = bindVV ps1 cs4 $ bindVV ps2 cs3 $ bindVV ps3 cs2 $ bindVV ps4 cs1
 $ bindLS pl1 cl1 $ bindLS pl2 cl2 $ bindLS pl3 cl3 $ bindLS pl4 cl4 emptyBinding
bindSpl2S
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4
 $ bindLN pl1     $ bindLS pl2 cl2 $ bindLN pl3     $ bindLN pl4     emptyBinding

bindVOneToOne
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4 emptyBinding

bind1toAll
 = bindLs pl1 [cl1,cl2,cl3,cl4]
 $ bindLN pl2     $ bindLN pl3     $ bindLN pl4       bindVOneToOne
bind2toAll
 = bindLs pl2 [cl1,cl2,cl3,cl4]
 $ bindLN pl1     $ bindLN pl3     $ bindLN pl4       bindVOneToOne
bind3toAll
 = bindLs pl3 [cl1,cl2,cl3,cl4]
 $ bindLN pl1     $ bindLN pl2     $ bindLN pl4       bindVOneToOne
bind4toAll
 = bindLs pl4 [cl1,cl2,cl3,cl4]
 $ bindLN pl1     $ bindLN pl2     $ bindLN pl3       bindVOneToOne

tst_vsMatch =
  testGroup "vsMatch"
    [ testCase "{} :: {} (OK)"
      ( nub (vsMatch [] emptyBinding b0 b0 S.empty S.empty) @?= [emptyBinding]  )
    , testCase "{} :: {ps1} (FAIL)"
      ( vsMatch [] emptyBinding b0 b0 S.empty (S.fromList [ps1]) @?= []  )
    , testCase "{cs1} :: {} (FAIL)"
      ( vsMatch [] emptyBinding b0 b0 (S.fromList [cs1]) S.empty @?= []  )
    , testCase "{cs1} :: {ps1} (OK)"
      ( nub (vsMatch [] emptyBinding b0 b0 (S.fromList [cs1]) (S.fromList [ps1])
          ::[Binding])
        @?= bindGVarToVList ps1 [cs1] emptyBinding  )
    , testCase "{cs2} :: {ps1} where ps1 |-> cs1 (FAIL)"
      ( vsMatch [] bindPSi2CSi b0 b0 (S.fromList [cs2]) (S.fromList [ps1]) @?= [] )
    , testCase "{cs2,cs1} :: {ps1,ps2} where ps_i |-> cs_i (OK)"
      ( nub (vsMatch [] bindPSi2CSi b0 b0
          (S.fromList [cs2,cs1]) (S.fromList [ps1,ps2]))
        @?= [bindPSi2CSi] )
    , testCase "{cs_i,cl_i} :: {ps_i,pl_i}, no pre-bind  (OK)"
      ( (set ( vsMatch [] emptyBinding b0 b0
               (S.fromList [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4])
               (S.fromList [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4]) ))
        -- 19 bindings possible, but only 4 generated
         @?= set [bindAllS,bind1toAll,bind2toAll,bind3toAll,bind4toAll] )
    , testCase "{cs_1,cs_2,cl_2,cs_3,cs_4} :: {ps_i,pl_i}, no pre-bind  (OK)"
      ( (nub ( vsMatch [] emptyBinding b0 b0
               (S.fromList [cs1,    cs2,cl2,cs3,    cs4])
               (S.fromList [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4]) )) !! 1
        @?= bindSpl2S )
    , testCase "{cs_i,cl_i} :: {ps_i,pl_i}, ps_i |-> cs_i  (OK)"
      ( (nub ( vsMatch [] bindPSSi2CSSi b0 b0
               (S.fromList [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4])
               (S.fromList [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4]) )) !! 0
        -- 19 bindings possible, with vlFreeMatchN where N=2
        -- 10th one returned is our bindAll
        @?= bindAllS)
    , testCase "{cs_i,cl_i} :: {ps_i,pl_i}, pl_i |-> {cl_i}  (OK)"
      ( nub ( vsMatch [] bindPSSi2CSSi b0 b0
               (S.fromList [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4])
               (S.fromList [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4]) )
        @?= [bindAllS] )
    , testCase "{cl_i} :: {pl_i}, no pre-bind  (OK)"
      ( set ( vsMatch [] emptyBinding b0 b0
               (S.fromList [cl1,cl2,cl3,cl4])
               (S.fromList [pl1,pl2,pl3,pl4]) )
        @?= set [ bind1to1
                , bindL1toAll
                , bindL2toAll
                , bindL3toAll
                , bindL4toAll
                ] )
    ]

bindL1toAll
 = bindLs pl1 [cl1,cl2,cl3,cl4]
 $ bindLN pl2 $ bindLN pl3 $ bindLN pl4 emptyBinding

bindL2toAll
 = bindLs pl2 [cl1,cl2,cl3,cl4]
 $ bindLN pl1 $ bindLN pl3 $ bindLN pl4 emptyBinding

bindL3toAll
 = bindLs pl3 [cl1,cl2,cl3,cl4]
 $ bindLN pl2 $ bindLN pl1 $ bindLN pl4 emptyBinding

bindL4toAll
 = bindLs pl4 [cl1,cl2,cl3,cl4]
 $ bindLN pl2 $ bindLN pl3 $ bindLN pl1 emptyBinding

bind1to1
 = bindLs pl1 [cl1]
 $ bindLs pl2 [cl2]
 $ bindLs pl3 [cl3]
 $ bindLs pl4 [cl4]
   emptyBinding

-- -----------------------------------------------------------------------------
tst_sMatch :: TF.Test


tst_sMatch
 = testGroup "\nsMatch"
   [ testCase "[42/y] :: [42/x] - succeeds"
     ( sMatch [] emptyBinding b0 b0 (k42_for y) (k42_for x)
       @?= Just (bindVV (StdVar x) (StdVar y) emptyBinding)
     )
   , testCase "[42/y] :: [58/x] - fails"
       ( sMatch [] emptyBinding b0 b0 (k42_for y) (k58_for x) @?= Nothing )
   , testCase "[42/a] :: [e/x] - succeeds"
     ( sMatch [] emptyBinding b0 b0 (k42_for a) (e_for x)
       @?=
       (Just ( bindVV (StdVar x) (StdVar a)
             $ bindVT (StdVar e) k42
             $ emptyBinding ))
     )
   , testCase "[58/b] :: [f/y] - succeeds"
     ( sMatch [] emptyBinding b0 b0 (k58_for b) (f_for y)
       @?=
       (Just ( bindVV (StdVar y) (StdVar b)
             $ bindVT (StdVar f) k58
             $ emptyBinding ))
     )
   , testCase "[42,58/a,b] :: [e,f/x,y] - succeeds 2 ways"
     ( nub ( sMatch [] emptyBinding b0 b0
              (fromJust $ substn [(a,k42),(b,k58)] [])
              (fromJust $ substn [ (x,ee), (y,ef)] []) )
       @?=
       ([ ( bindVV (StdVar x) (StdVar a)
          $ bindVT (StdVar e) k42
          $ bindVV (StdVar y) (StdVar b)
          $ bindVT (StdVar f) k58
          $ emptyBinding )
        , ( bindVV (StdVar x) (StdVar b)
           $ bindVT (StdVar e) k58
           $ bindVV (StdVar y) (StdVar a)
           $ bindVT (StdVar f) k42
           $ emptyBinding )
        ])
     )
   , testCase "[las/lbs] :: [l1s/l2s]  - STATIC succeeds"
       ( nub ( sMatch [] emptyBinding b0 b0
                  (fromJust $ substn [] [(lbs,las)])
                  (fromJust $ substn [] [(l2s,l1s)]) )
       @?= [ ( bindLL (LstVar l2s) (LstVar lbs)
             $ bindLSR (LstVar l1s) [] [las] $ emptyBinding) ]
       )
   , testCase "[la/lb] :: [l1/l2]  - succeeds"
       ( nub ( sMatch [] emptyBinding b0 b0
                  (fromJust $ substn [] [(lb,la)])
                  (fromJust $ substn [] [(l2,l1)]) )
       @?= [ ( bindLL (LstVar l2) (LstVar lb)
             $ bindLSR (LstVar l1) [] [la] $ emptyBinding) ]
       )
   , testCase "[la/lb] :: [e/x]  - fails"
       ( sMatch [] emptyBinding b0 b0
           (fromJust $ substn []       [(lb,la)])
           (fromJust $ substn [(x,ee)] []       )
         @?=  Nothing )
   , testCase "[42,la/a,lb] :: [e,l1/x,l2]  - succeeds"
       ( nub ( sMatch [] emptyBinding b0 b0
                 (fromJust $ substn [(a,k42)] [(lb,la)])
                 (fromJust $ substn [(x,ee)] [(l2,l1)]) )
         @?=
         ([ ( bindVV (StdVar x) (StdVar a)
            $ bindLL (LstVar l2) (LstVar lb)
            $ bindVT (StdVar e) k42
            $ bindLSR (LstVar l1) [] [la]
            $ emptyBinding )])
       )
   ]


-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nMatching  (candidate :: pattern)"
      [ tst_match
      , tst_tsMatch
      , tst_collMatch
      , tst_vMatchVm
      , tst_tvMatch
      , tst_vMatchGI
      , tst_vlMatch
      , tst_vsMatch
      , tst_sMatch
      ]
    ]

tstMatch = defaultMain tst_Matching
