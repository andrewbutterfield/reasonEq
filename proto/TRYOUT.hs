module TRYOUT where
{- To help with debugging -}
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S

--import Utilities
import LexBase
import Variables
import AST
import VarData
import Binding
import Matching

import NiceSymbols


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

{- Some zipper stuff -}

--  t = Tree(t) = 1 + Zt^2
data Tree
  = Nowt | Bush Tree Int Tree
  deriving Show

showTree Nowt = "."
showTree (Bush left i right)
  = treeShow (showTree left) (show i) (showTree right)

treeShow l i r  =  wrap l ++ "<-" ++ i ++ "->" ++ wrap r
wrap s = "("++s++")"

putTree = putStrLn . showTree

-- dTree(t)/dt = 2Zt
data Tree'
  = Bush' Dir Int Tree
  deriving Show

showTree' (t,wayup) = showTree'' (highlight $ showTree t) wayup
showTree'' substr [] = substr
showTree'' substr (Bush' One i right : wayup)
  = showTree'' (treeShow substr (show i) (showTree right)) wayup
showTree'' substr (Bush' Two i left : wayup)
  = showTree'' (treeShow (showTree left) (show i) substr ) wayup

highlight s = bold ("@@@:"++s++":@@@")

putTree' = putStrLn . showTree'

data Dir = One | Two deriving Show ; l = One ; r = Two

type Zip = (Tree,[Tree'])

start :: Tree -> Zip
start t = (t,[])

down :: Dir -> Zip -> Zip
down _ (Nowt,wayup) = (Nowt,wayup)
down One (Bush left i right,wayup) = (left, Bush' One i right : wayup)
down Two (Bush left i right,wayup) = (right,Bush' Two i left  : wayup)

up :: Zip -> Zip
up (t,[]) = (t,[])
up (t,Bush' One i right : wayup) = (Bush    t i right, wayup)
up (t,Bush' Two i left  : wayup) = (Bush left i t,     wayup)

stop :: Zip -> Tree
stop (t,[]) = t
stop z = stop $ up z

leaf i = Bush Nowt i Nowt
t1 i = Bush (leaf (i-1)) i (leaf (i+1))
t2 i = Bush (t1 (i-2)) i (t1 (i+2))

mytree = t2 3
