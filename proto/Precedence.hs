module Precedence where

import Data.List

data Exp
 = A Char
 | C Char [Exp]
 deriving (Eq,Ord,Show)

data OpData
 = OD { op :: Char
      , prec :: Int
      , isAssoc :: Bool
      , isLAssoc :: Bool
      , isRAssoc :: Bool
      , isSymm :: Bool
      }
  deriving (Eq,Ord,Show)


opdata
  = [ OD '+' 6 False True  False True  -- infixl, symm
    , OD '-' 6 False True  False False -- infixl, not-symm
    , OD '*' 7 False True  False True  -- infixl, symm
    , OD '/' 7 False True  False False -- infixl, not-symm
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

add x y = C '+' [x,y]
sub x y = C '-' [x,y]
mul x y = C '*' [x,y]
dvd x y = C '/' [x,y]
 
pp :: Exp -> String
pp exp = ppp 0 exp

ppp p (A c) = [c]
ppp p (C n es) 
  = case od n of
      Nothing ->  n:"("++intercalate "," (map (ppp 0) es)++")"
      Just od -> "od-nyi"