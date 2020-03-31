module TestDefs
where

import Data.Maybe(fromJust)
import Data.Map (Map)
import Data.Map as M (fromList)
import Data.Set (Set)
import Data.Set as S (empty,fromList,singleton)

import LexBase
import Variables
import AST
import VarData
import Binding

-- ========== VALUES ==============

-- ----------- Identifier -------

u = jId "u"
v = jId "v"

-- --------- Variable ----------

osv = ObsVar  (jId "osv") Static
osu = ObsVar  (jId "osu") Static
esv = ExprVar (jId "esv") Static
psv = PredVar (jId "psv") Static

obv  = ObsVar (jId "obv" )   Before
odmv = ObsVar (jId "odmv") $ During "m"
odnv = ObsVar (jId "odnv") $ During "n"
oav  = ObsVar (jId "oav" )   After
otv  = ObsVar (jId "otv" )   Textual

ob_u = ObsVar u Before; oa_u = ObsVar u After; odm_u = ObsVar u $ During "m"
ob_v = ObsVar v Before; oa_v = ObsVar v After; odm_v = ObsVar v $ During "m"

obu = ObsVar  (jId "obu") Before
ebv = ExprVar (jId "ebv") Before
pbv = PredVar (jId "pbv") Before

-- ------------- ListVar ---------------

lobv = PreVars $ jId "lobv"
lebv = PreExprs $ jId "lebv"
lpbv = PrePreds $ jId "lpbv"

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

jId :: String -> Identifier
jId = fromJust . ident

sngl :: a -> Set a
sngl = S.singleton

-- --------  Update variable During 'subscript' (partial) -----------

vDurRen  :: String -> Variable -> Variable
lvDurRen :: String -> ListVar  -> ListVar
gvDurRen :: String -> GenVar   -> GenVar

vDurRen  n (Vbl i vw (During _))  =  Vbl i vw $ During n
lvDurRen n (LVbl v is ij)         =  LVbl (vDurRen n v) is ij
gvDurRen n (StdVar v)             =  StdVar $ vDurRen n v
gvDurRen n (LstVar lv)            =  LstVar $ lvDurRen n lv

-- ---- (mostly) partial Binding updaters ------

bindVV :: GenVar -> GenVar   -> Binding -> Binding
bindVT :: GenVar -> Term     -> Binding -> Binding
bindLL :: GenVar -> GenVar   -> Binding -> Binding
bindLl :: GenVar -> [GenVar] -> Binding -> Binding
bindL0 :: GenVar             -> Binding -> Binding
bindLS :: GenVar -> GenVar   -> Binding -> Binding
bindLs :: GenVar -> [GenVar] -> Binding -> Binding
bindLN :: GenVar             -> Binding -> Binding
bindLT :: GenVar -> Term     -> Binding -> Binding
bindLt :: GenVar -> [Term]   -> Binding -> Binding

bindVV (StdVar pv)  (StdVar cv)   =  fromJust . bindVarToVar pv cv
bindVT (StdVar pv)  ct    =  fromJust . bindVarToTerm pv ct
bindLL (LstVar plv) cgv   =  fromJust . bindLVarToVList plv [cgv]
bindLl (LstVar plv) cgvs  =  fromJust . bindLVarToVList plv cgvs
bindL0 (LstVar plv)       =  fromJust . bindLVarToVList plv []
bindLS (LstVar plv) cgv   =  fromJust . bindLVarToVSet plv (S.singleton cgv)
bindLs (LstVar plv) cgvs  =  fromJust . bindLVarToVSet plv (S.fromList cgvs)
bindLN (LstVar plv)       =  fromJust . bindLVarToVSet plv S.empty
bindLT (LstVar plv) ct    =  fromJust . bindLVarToTList plv [ct]
bindLt (LstVar plv) cts   =  fromJust . bindLVarToTList plv cts

bindLSR :: GenVar -> [Term] -> [ListVar] -> Binding -> Binding
bindLSR (LstVar plv) ctsub crpl = fromJust . bindLVarSubstRepl plv ctsub crpl


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
