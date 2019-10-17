module MkTestBind
 ( bindVV, bindLL, bindLl, bindVT, bindL0, bindLS, bindLs, bindLN, bindLT, bindLt
 -- , bindLLSub
 , vDurRen, lvDurRen, gvDurRen
 )
where

import Data.Maybe(fromJust)
import qualified Data.Set as S

import AST
import Variables
import Binding

-- (mostly) partial functions for use in tests

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

-- bindLLSub (LstVar tplv,LstVar rplv) ctermsub clvarsub
--  = fromJust . b'' (LstVar tplv,LstVar rplv) ctermsub clvarsub
-- b'' (LstVar tplv,LstVar rplv) ctermsub clvarsub
--  = bindLVarPairSubst tplv rplv (S.fromList ctermsub) (S.fromList clvarsub)
--    , testCase "bindLLSub works properly" (True @?= False)


vDurRen  :: String -> Variable -> Variable
lvDurRen :: String -> ListVar  -> ListVar
gvDurRen :: String -> GenVar   -> GenVar

vDurRen  n (Vbl i vw (During _))  =  Vbl i vw $ During n
lvDurRen n (LVbl v is ij)         =  LVbl (vDurRen n v) is ij
gvDurRen n (StdVar v)             =  StdVar $ vDurRen n v
gvDurRen n (LstVar lv)            =  LstVar $ lvDurRen n lv
