module TRYOUT where
{- To help with debugging -}
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S

--import Utilities
import LexBase
import AST
import VarData
import Binding
import Matching


-- Variables
va = PreVar $ fromJust $ ident "a"
vb = PreVar $ fromJust $ ident "b"
vc = PreVar $ fromJust $ ident "c"

-- ListVar
la = PreVars $ fromJust $ ident "a"
lb = PreVars $ fromJust $ ident "b"
lc = PreVars $ fromJust $ ident "c"

-- GenVar
gva = StdVar va
gvb = StdVar vb
gvc = StdVar vc
gla = LstVar la
glb = LstVar lb
glc = LstVar lc
