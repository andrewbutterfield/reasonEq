module Precedence where

import Data.List

data Exp
 = A Char
 | C Char [Exp]
 deriving (Eq,Ord,Show)

data Fix 
  = N -- none
  | L -- left-assoc
  | R -- right-assoc
  deriving (Eq,Ord,Show)

data OpData
 = OD { op :: Char
      , prec :: Int
      , fixity :: Fix
      }
  deriving (Eq,Ord,Show)


-- preludeFixities = concat
--     [infixr_ 9  ["."]
--     ,infixl_ 9  ["!!"]
--     ,infixr_ 8  ["^","^^","**"]
--     ,infixl_ 7  ["*","/","`quot`","`rem`","`div`","`mod`"]
--     ,infixl_ 6  ["+","-"]
--     ,infixr_ 5  [":","++"]
--     ,infix_  4  ["==","/=","<","<=",">=",">","`elem`","`notElem`"]
--     ,infixl_ 4  ["<$>","<$","<*>","<*","*>"]
--     ,infixr_ 3  ["&&"]
--     ,infixr_ 2  ["||"]
--     ,infixl_ 1  [">>",">>="]
--     ,infixr_ 1  ["=<<"]
--     ,infixr_ 0  ["$","$!","`seq`"]
--     ]

-- operator precedences are always > 0
-- top-level or just inside parentheses is = 0
opdata
  = [ OD '=' 4 N
    , OD ':' 5 L
    , OD '+' 6 L
    , OD '-' 6 L
    , OD '*' 7 L
    , OD '/' 7 L
    , OD '^' 8 R
    ]

olkp :: [OpData] -> Char -> Maybe OpData
olkp [] _ = Nothing
olkp (od:ods) opr
  | opr == op od = Just od
  | otherwise    =  olkp ods opr

od = olkp opdata

pfx :: Exp -> String
pfx (A c) = [c]
pfx (C n es) = n:"("++intercalate "," (map pfx es)++")"

x = A 'x'
y = A 'y'
z = A 'z'
a = A 'a'
b = A 'b'
c = A 'c'
d = A 'd'
f = 'f'

add x y   =  C '+' [x,y]
sub x y   =  C '-' [x,y]
mul x y   =  C '*' [x,y]
dvd x y   =  C '/' [x,y]
eql x y   =  C '=' [x,y]
cns x y   =  C ':' [x,y]
xpn x y   =  C '^' [x,y]
app f es  
  = case od f of
     Just (OD _ _ N)
       | length es /= 2  ->  C '?' (A f:es)
     _                   ->  C f es
adds es = app '+' es
muls es = app '*' es
xpns es = app '^' es
neg  e  = app '_' [e]

pp :: Exp -> String
pp exp = ppp 0 exp

ppp p (A c) = [c]
ppp p (C n es) 
  = case od n of
      Nothing           ->  ppapp         n es
      Just (OD _ p' N)  ->  ppinfix  p p' n es
      Just (OD _ p' L)  ->  pplinfix p p' n es
      Just (OD _ p' R)  ->  pprinfix  p p' n es

pplinfix p p' n (C n' fs:es) 
  | n == n' = pplinfix p p' n (fs++es)
pplinfix p p' n es = ppinfix p p' n es

pprinfix p p' n es@(_:_:_)
  = case esL of
      (C n' fs) | n == n' -> pprinfix p p' n (es'++fs)
      _                   -> ppinfix p p' n es
  where
    (es',esL) = splitAtEnd es
pprinfix p p' n es = ppinfix p p' n es

splitAtEnd [x,y] = ([x],y)
splitAtEnd (x:xs) 
  =  let (xs',y) = splitAtEnd xs
     in (x:xs',y)

-- treat negation seperately (also lnot?)
ppapp '_' [A n]  =  ['_',n]
ppapp '_' [e]    =  "_("++ppp 0 e++")"
ppapp n es       =  n:"("++intercalate "," (map (ppp 0) es)++")"
ppinfix p p' n es
  | p' <= p    =  "("++intercalate [' ',n,' '] (map (ppp 0)  es)++")"
  | otherwise  =       intercalate [' ',n,' '] (map (ppp p') es)

-- test cases

testcases
  = [ ( a, "a" )
    , ( neg a, "_a" )
    , ( neg (add a b), "_(a+b)" )
    , ( add a b, "a+b" )
    , ( add (mul a b) (mul c d) , "a*b+c*d" )
    , ( mul (add a b) (add c d) , "(a+b)*(c+d)" )
    , ( add (add a b) c, "a+b+c" )
    , ( add a (add b c), "a+(b+c)" )
    , ( sub (sub a b) c, "a-b-c" )
    , ( sub a (sub b c), "a-(b-c)")
    , ( xpn (xpn a b) c, "(a^b)^c)" )
    , ( xpn a (xpn b c), "a^b^c" )
    ]

runtest ( t, expected )
  = putStrLn $ unlines 
      [ "----------"
      , show t
      , "--"
      , "pfx: "++pfx t
      , "pp: "++pp t 
      , "expected: "++expected
      ]

runtests [] = return ()
runtests (t:ts) = runtest t >> runtests ts

testall = runtests testcases