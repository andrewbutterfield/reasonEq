module TestDefs
where

import Data.Maybe(fromJust)
import Data.Map (Map)
import Data.Map as M (fromList)
import Data.Set (Set)
import Data.Set as S (singleton)

import LexBase
import Variables
import AST
import VarData
import Binding

-- ========== VALUES ==============

-- ----------- Identifier -------

u = fromJust $ ident "u"
v = fromJust $ ident "v"

-- --------- Variable ----------

osv = ObsVar  (fromJust $ ident "osv") Static
osu = ObsVar  (fromJust $ ident "osu") Static
esv = ExprVar (fromJust $ ident "esv") Static
psv = PredVar (fromJust $ ident "psv") Static

obv  = ObsVar (fromJust $ ident "obv" )   Before
odmv = ObsVar (fromJust $ ident "odmv") $ During "m"
odnv = ObsVar (fromJust $ ident "odnv") $ During "n"
oav  = ObsVar (fromJust $ ident "oav" )   After
otv  = ObsVar (fromJust $ ident "otv" )   Textual

ob_u = ObsVar u Before; oa_u = ObsVar u After; odm_u = ObsVar u $ During "m"
ob_v = ObsVar v Before; oa_v = ObsVar v After; odm_v = ObsVar v $ During "m"

obu = ObsVar  (fromJust $ ident "obu") Before
ebv = ExprVar (fromJust $ ident "ebv") Before
pbv = PredVar (fromJust $ ident "pbv") Before

-- ------------- ListVar ---------------

lobv = PreVars $ fromJust $ ident "lobv"
lebv = PreExprs $ fromJust $ ident "lebv"
lpbv = PrePreds $ fromJust $ ident "lpbv"

-- ----------- GenVar ----------------

gosu = StdVar osu
gesv = StdVar esv
gpsv = StdVar psv

gobu = StdVar obu
gebv = StdVar ebv
gpbv = StdVar pbv

-- ------------ Expressions (Term) -----------

ce42 = EVal ArbType $ Integer 42

-- ------------- Predicates (Term) ------------

pTrue = PVal $ Boolean True


-- ================ FUNCTIONS =======================


-- --------------- Function Shorthands --------------

sngl :: a -> Set a
sngl = S.singleton

-- ------------ Lookup after Bind ----------------

bindLook :: (t1 -> t2 -> Maybe a) -> (t2 -> t3 -> Binding -> Maybe t1)
         -> t2 -> t3 -> a
bindLook lkp bind pv cx
 = fromJust (lkp (fromJust (bind pv cx emptyBinding)) pv)

bindLook2 :: (t1 -> t2 -> Maybe a) -> (t3 -> t4 -> Binding -> Maybe t1)
          -> t3 -> t4 -> t2 -> a
bindLook2 lkp bind pv1 cx pv2
 = fromJust (lkp (fromJust (bind pv1 cx emptyBinding)) pv2)

vtBindLook :: Variable -> Term -> VarBind
vtBindLook = bindLook lookupVarBind bindVarToTerm

vvBindLook :: Variable -> Variable -> VarBind
vvBindLook = bindLook lookupVarBind bindVarToVar

vvBindLook2 :: Variable -> Variable -> Variable -> VarBind
vvBindLook2 = bindLook2 lookupVarBind bindVarToVar

llBindLook :: ListVar -> VarList -> LstVarBind
llBindLook = bindLook lookupLstBind bindLVarToVList

lsBindLook :: ListVar -> VarSet -> LstVarBind
lsBindLook = bindLook lookupLstBind bindLVarToVSet
