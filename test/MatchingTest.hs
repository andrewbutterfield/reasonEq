module MatchingTest ( tst_Matching )
where

import Data.Maybe(fromJust)
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
tst_tvMatch, tst_vMatchVm, tst_vMatchGI :: TF.Test

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
        ( (tvMatch [vt] emptyBinding b0 b0 true okk ok :: [Binding] )
          @?= bindVarToTerm ok true emptyBinding )
      , testCase "true :: g1, known (Ok)"
        ( (tvMatch [vt] emptyBinding b0 b0 true okk ok :: [Binding] )
          @?= bindVarToTerm ok true emptyBinding )
      ]

g1 = Vbl (fromJust $ ident "g1") ObsV Static
i11 = Vbl (fromJust $ ident "i11") ObsV Static
i12 = Vbl (fromJust $ ident "i12") ObsV Static
g2 = Vbl (fromJust $ ident "g2") ObsV Static
i2 = Vbl (fromJust $ ident "i2") ObsV Static
g3 = Vbl (fromJust $ ident "g3") ObsV Static
i3 = Vbl (fromJust $ ident "i3") ObsV Static

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
identi nm i = fromJust $ ident (nm++show i)
mkPS i = StdVar $ PreVar  $ identi "ps" i
mkPL i = LstVar $ PreVars $ identi "pl" i
mkCS i = StdVar $ PreVar  $ identi "cs" i
mkCL i = LstVar $ PreVars $ identi "cl" i
bindVV (StdVar pv)  (StdVar cv)   =  fromJust . bindVarToVar pv cv
bindLL (LstVar plv) cgv  =  fromJust . bindLVarToVList plv [cgv]
bindL0 (LstVar plv)      =  fromJust . bindLVarToVList plv []


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

bindLs (LstVar plv) cgvs  =  fromJust . bindLVarToVSet plv (S.fromList cgvs)
bindLS (LstVar plv) cgv   =  fromJust . bindLVarToVSet plv (S.singleton cgv)
bindLN (LstVar plv)       =  fromJust . bindLVarToVSet plv S.empty

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

bind1toAll
 = bindVV ps1 cs1 $ bindVV ps2 cs2 $ bindVV ps3 cs3 $ bindVV ps4 cs4
 $ bindLs pl1 [cl1,cl2,cl3,cl4]
 $ bindLN pl2     $ bindLN pl3     $ bindLN pl4       emptyBinding

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
      ( (nub ( vsMatch [] emptyBinding b0 b0
               (S.fromList [cs1,cl1,cs2,cl2,cs3,cl3,cs4,cl4])
               (S.fromList [ps1,pl1,ps2,pl2,ps3,pl3,ps4,pl4]) )) !! 0
        -- 19 bindings possible, but only 4 generated
        -- 1st one returned is our bind1toAll
        @?= bind1toAll )
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
      ( nub ( vsMatch [] emptyBinding b0 b0
               (S.fromList [cl1,cl2,cl3,cl4])
               (S.fromList [pl1,pl2,pl3,pl4]) )
        @?= [ bindL1toAll
            , bindL2toAll
            , bindL3toAll
            , bindL4toAll
            , bind1to1
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

k42_for v = fromJust $ substn [(v,k42)] []
k58_for v = fromJust $ substn [(v,k58)] []
e =  ExprVar (fromJust $ ident "e") Static
f =  ExprVar (fromJust $ ident "f") Static
ee = fromJust $ eVar ArbType e
ef = fromJust $ eVar ArbType f
e_for v = fromJust $ substn [(v,fromJust $ eVar ArbType $ e)] []
bindVT (StdVar pv)  ct   =  fromJust . bindVarToTerm pv ct
a = PreVar $ fromJust $ ident "a"
b = PreVar $ fromJust $ ident "b"

l1 = PreVars $ fromJust $ ident "l1"
l2 = PreVars $ fromJust $ ident "l2"
la = PreVars $ fromJust $ ident "la"
lb = PreVars $ fromJust $ ident "lb"

tst_sMatch
 = testGroup "\nsMatch"
   [ testCase "[42/y] :: [42/x] - succeeds"
     ( sMatch [] emptyBinding b0 b0 (k42_for y) (k42_for x)
       @?= Just (bindVV (StdVar x) (StdVar y) emptyBinding)
     )
   , testCase "[42/y] :: [58/x] - fails"
       ( sMatch [] emptyBinding b0 b0 (k42_for y) (k58_for x) @?= Nothing )
   , testCase "[42/y] :: [e/x] - succeeds"
     ( sMatch [] emptyBinding b0 b0 (k42_for y) (e_for x)
       @?=
       (Just ( bindVV (StdVar x) (StdVar y)
             $ bindVT (StdVar e) k42
             $ emptyBinding ))
     )
   , testCase "[42,58/a,b] :: [e,f/x,y] - succeeds (One way only for now)"
     ( nub ( sMatch [] emptyBinding b0 b0
              (fromJust $ substn [(a,k42),(b,k58)] [])
              (fromJust $ substn [ (x,ee), (y,ef)] []) )
       @?=
       ([ ( bindVV (StdVar x) (StdVar a)
          $ bindVT (StdVar e) k42
          $ bindVV (StdVar y) (StdVar b)
          $ bindVT (StdVar f) k58
          $ emptyBinding )
        ])
     )
   , testCase "[la/lb] :: [l1/l2]  - succeeds"
       ( nub ( sMatch [] emptyBinding b0 b0
                  (fromJust $ substn [] [(lb,la)])
                  (fromJust $ substn [] [(l2,l1)]) )
       @?= [ ( bindLS (LstVar l1) (LstVar la)
                 $ bindLS (LstVar l2) (LstVar lb)
                 $ emptyBinding  ) ]
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
            $ bindVT (StdVar e) k42
            $ bindLS (LstVar l1) (LstVar la)
            $ bindLS (LstVar l2) (LstVar lb)
            $ emptyBinding )])
       )
   ]


-- -----------------------------------------------------------------------------
tst_Matching :: [TF.Test]

tst_Matching
  = [ testGroup "\nMatching  (candidate :: pattern)"
      [ tst_match
      , tst_tsMatch
      , tst_vMatchVm
      , tst_tvMatch
      , tst_vMatchGI
      , tst_vlMatch
      , tst_vsMatch
      , tst_sMatch
      ]
    ]

tstMatch = defaultMain tst_Matching
