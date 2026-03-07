\chapter{Pretty Printer}
\begin{code}
module PrettyPrint
 ( Style(..)
 , styleRed, styleMagenta
 , PP(..), PP'(..)
 , ppa,pad,pps,ppc
 , ppnul,ppopen',ppopen,ppsopen,pplist,ppbracket,ppclosed
 , paren
 , renderIn,render )
where
import Utilities
import Data.List
\end{code}

\begin{code}
ind i = replicate i ' '
\end{code}

Our pretty printer handles atomic pieces, which render as is,
and composite parts, defined as a list of parts, along with descriptions
of the left and right delimiters and a separator part.
Composites will be rendered with line breaks and indentation
in a manner that is hopefully maximally pleasing.
We also provide a (simple) means for applying ``styles''.

\section{Styles}

For now we use ANSI escape sequences to apply styles.
This works fine in an OS X Terminal,
but doesn't work in a DOS Window.
\begin{code}
data Style = Underline
           | Colour Char
           deriving (Eq,Ord,Show)

styleRed     = Colour '1'
styleGreen   = Colour '2'
styleBlue    = Colour '4'
styleYellow  = Colour '3'
styleMagenta = Colour '5'
styleCyan    = Colour '6'
styleWhite   = Colour '7' --light grey!!
\end{code}

Implementation details
\begin{code}
showStyle :: Style -> String
showStyle Underline   =  setUnderline
showStyle (Colour c)  =  setColour c

resetStyle :: String
resetStyle            =  "\ESC[m\STX"
setUnderline          =  "\ESC[4m\STX"
setColour colourCode  =  "\ESC[3"++colourCode:"m\STX"

setStyle :: [Style] -> String
--setStyle  = concat . reverse . map showStyle
setStyle  = concat . map showStyle
reset = putStrLn resetStyle -- useful in GHCi to tidy up!
\end{code}


\section{Pretty-Printing Types}

\begin{eqnarray*}
  pp &::=& pp_{atom} |  pp_{ldelim} ~ pp_{delim} ~ pp_{sep} ~ pp^*
\end{eqnarray*}
We implement these using two mutually recursive datatypes where
the top level-one (\h{PP}) wraps the above structure with an integer that gives the
rendered length of the structure, at each level.
\begin{code}
data PP = PP Int PP' deriving (Eq,Ord,Show)

data PP' = PPA String          -- atom
         | PPS Style PP       -- style
         | PPC PP PP PP [PP]  -- rdelim ldelim sep pps
         deriving (Eq,Ord,Show)

-- useful query
ppsize :: PP -> Int
ppsize (PP s _) = s
\end{code}


\section{Smart Constructors}

We build smart versions of the \h{PPA}, \h{PPS} and \h{PPC}
constructors
that automatically accumulate the length information.
\begin{code}
ppa :: String -> PP
ppa str = PP (length str) $ PPA str

pps :: Style -> PP -> PP
pps style pp@(PP len _) = PP len $ PPS style pp

ppc :: PP -> PP -> PP -> [PP] -> PP
ppc lpp rpp sepp pps
 = PP pplen $ PPC lpp rpp sepp pps
 where
  pplen = ppsize lpp + ppsize rpp + seps pps * ppsize sepp
          + sum (map ppsize pps)
  seps xs
   | len == 0  =  0
   | otherwise  =  len - 1
   where len = length xs
\end{code}

A useful utility for putting (single) spacec around things (typically operators):
\begin{code}
pad :: String -> String
pad s = ' ':s++" "
\end{code}

We then provide some useful builders for common idioms,
mostly where delimiters and separators are atomic.
\begin{code}
ppnul :: PP -- the empty string
ppnul = ppa ""

ppopen' :: PP -> [PP] -> PP
ppopen' = ppc ppnul ppnul

ppopen :: String -> [PP] -> PP
ppopen sepstr pps = ppopen' (ppa sepstr) pps

ppsopen :: Style -> String -> [PP] -> PP
ppsopen style sepstr ppp = ppopen' (pps style $ ppa sepstr) ppp

pplist :: [PP] -> PP
pplist = ppopen ""

ppbracket :: String -> PP -> String -> PP
ppbracket lbr pp rbr = ppclosed lbr rbr "" [pp]

ppclosed :: String -> String -> String -> [PP] -> PP
ppclosed lstr rstr sepstr pps
  = ppc (ppa lstr) (ppa rstr) (ppa sepstr) pps
\end{code}
Code to add parentheses when required by a change in current precedence level.
This assume that lower precedence values mean looser binding,
so if the inner is looser than the outer we need to bracket it.
\begin{code}
paren :: Int -> Int -> PP -> PP
paren outerp innerp (PP w (PPC _ _ sepp pps))
 | innerp < outerp  =  ppc (ppa "(") (ppa ")") sepp pps
paren outerp innerp pp = pp
\end{code}



\section{Simple Rendering}

It is useful to get the string produced
if a \h{PP} is all rendered on one line.
\begin{code}
ppstr :: [Style] -> PP -> String

ppstr _ (PP _ (PPA str)) = str

ppstr stls (PP _ (PPS style pp))
 = concat [ showStyle style -- set new style style
          , ppstr (style:stls) pp -- recurse with styles updated
          , resetStyle -- clear all styles
          , setStyle stls -- restore current style
          ]

ppstr stls (PP _ (PPC lpp rpp sepp []))
                              = ppstr stls lpp ++ ppstr stls rpp

ppstr stls (PP _ (PPC lpp rpp sepp pps))
 | ppsize lpp == 0  =  pppps stls rpp sepp pps
 | otherwise        =  ppstr stls lpp ++ pppps stls rpp sepp pps
 where

  pppps :: [Style] -> PP -> PP -> [PP] -> String
  pppps stls rpp sepp []        =  ppstr stls rpp
  pppps stls rpp sepp [pp]      =  ppstr stls pp ++ ppstr stls rpp
  pppps stls rpp sepp (pp:pps)
    =  ppstr stls pp ++ ppstr stls sepp ++ pppps stls rpp sepp pps
\end{code}



\section{Full Rendering}

Now, rendering it as a `nice' string.
We provide the desired column width at the top level,
along with an specified initial indentation
or one set to zero.
\begin{code}
renderIn :: Int -> Int -> PP -> String
renderIn w0 ind = fmtShow . layout [] (w0-ind) ind

render :: Int -> PP -> String
render w0 = renderIn w0 0
\end{code}

\subsection{Lines and Formatting}

We have atomic strings present,
and we also need to explicitly identify newlines and indents.
All of these need to have an associated style.
\begin{code}
data Layout = NL | Ind Int | Txt String deriving Show

type SLayout = (Layout,[Style])
\end{code}
We obtain the final string by merging \h{Fmt} with \h{Txt} on either
side before calling \h{unlines}
(otherwise formatting commands introduce spurious linebreaks).
\begin{code}
lstr NL         =  "\n"
lstr (Ind i)    =  ind i
lstr (Txt str)  =  str

fmtShow :: [SLayout] -> String
fmtShow = concat . fshow []
 where
   fshow [] [] = []
   fshow _  [] = [resetStyle]
   fshow ss ((layout,ss'):slayouts)
    | ss == ss'  =  lstr layout :  fshow ss' slayouts
    | otherwise
       = resetStyle : setStyle ss' : lstr layout : fshow ss' slayouts
\end{code}

\paragraph{List viewer}

Show list elements one per line:
\begin{code}
ldisp :: Show a => [a] -> IO ()
ldisp = putStrLn . unlines' . map show
\end{code}


\subsection{Layout}

The main recursive layout algorithm has a width and indentation parameter
---
the sum of these is always constant.
\begin{code}
-- w+i is constant;  w+i=w0 above
layout :: [Style] ->Int -> Int -> PP -> [SLayout]

-- handle style changes
layout ss w i (PP _ (PPS s pp)) = layout (s:ss) w i pp

-- 1st three cases: cannot break, or can fit on line
layout ss _ i (PP _ (PPA str))          =  [(Txt str,ss)]
layout ss _ i pp@(PP _ (PPC _ _ _ []))  =  [(Txt $ ppstr ss pp, ss)]
layout ss w i pp@(PP s _)  | s <= w     =  [(Txt $ ppstr ss pp, ss)]

-- case when non-trivial comp and it is too wide
layout ss w i (PP _ (PPC lpp rpp sepp pps))
 = layout' ss w i (w-s) (i+s) lpp rpp sepp pps -- pps not null
 where s = max (ppsize lpp) (ppsize sepp)
\end{code}

The helpers, \h{layout'} and \h{layout''}
need to track outer (\h{w i}) and inner (\h{w' i'}) values
of width and indentation.
\begin{code}
-- we need to split it up

-- singleton case:   lpp \n pp \n rpp
layout' ss w i w' i' lpp rpp sepp [pp]
 = layout ss w i lpp
   ++ (NL,ss) : (Ind i',ss) : layout ss w' i' pp
   ++ (NL,ss) : (Ind i, ss) : layout ss w i rpp

-- general case
layout' ss w i w' i' lpp@(PP lw _) rpp sepp (pp:pps)
 = (Txt $ ppstr ss lpp, ss) : (Ind (i'-(i+lw)),ss) -- header line
                        : (layout ss w' i' pp)
   ++
   (NL,ss) : layout'' ss w i w' i' rpp sepp pps -- pps not null

layout'' ss w i w' i' rpp@(PP rw _) sepp@(PP sw _) [pp]
 = (Ind i,ss) : (Txt $ ppstr ss sepp, ss)
                    : (Ind (i'-(i+sw)),ss) : layout ss w' i' pp
   ++ [(Txt $ ppstr ss rpp,ss)]

layout'' ss w i w' i' rpp sepp@(PP sw _) (pp:pps)
 = (Ind i,ss) : (Txt $ ppstr ss sepp, ss)
                    : (Ind (i'-(i+sw)),ss) : layout ss w' i' pp
   ++
   (NL,ss) : layout'' ss w i w' i' rpp sepp pps -- pps not null
\end{code}
