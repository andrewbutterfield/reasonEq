module OneForAll where

something a = (a,42)
nothing a = (a,0)

somethings = map something
nothings = map nothing

pvars = "abcdefg"

ileave summat nowt -- length summat == length nowt
 = ileave' [] nowt summat

ileave' before [] [] = [] -- length summat == length nowt
ileave' before (n:nowt) (s:summat)  -- length summat == length nowt
 = (reverse before ++ s : nowt)
   :
   ileave' (n:before) nowt summat

{-

ileave (somethings pvars) (nothings pvars) =

[[('a',42),('b',0),('c',0),('d',0),('e',0),('f',0),('g',0)]
,[('a',0),('b',42),('c',0),('d',0),('e',0),('f',0),('g',0)]
,[('a',0),('b',0),('c',42),('d',0),('e',0),('f',0),('g',0)]
,[('a',0),('b',0),('c',0),('d',42),('e',0),('f',0),('g',0)]
,[('a',0),('b',0),('c',0),('d',0),('e',42),('f',0),('g',0)]
,[('a',0),('b',0),('c',0),('d',0),('e',0),('f',42),('g',0)]
,[('a',0),('b',0),('c',0),('d',0),('e',0),('f',0),('g',42)]
]

However, this ignores the fact that we have one binding at the end.

-}
