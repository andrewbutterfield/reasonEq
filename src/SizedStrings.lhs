\chapter{Sized String Structures}
\begin{code}
module SizedStrings
 ( Style(..)
 , styleRed, styleMagenta
 , showStyle
 , resetStyle, setUnderline, setColour
 , setStyle
 , SS(..), SS'(..)
 , ssa,pad,sss,ssc
 , ssnul,ssopen',ssopen,sssopen,sslist,ssbracket,ssclosed
 , paren
 , ss2str, ss'2str
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

\newpage
Implementation details
\begin{code}
showStyle :: Style -> String
showStyle Underline   =  setUnderline
showStyle (Colour c)  =  setColour c

-- \ESC[ is CSI ;  \ESC[Xm  is CSI X m  or SGR
resetStyle            =  "\ESC[m\STX"
setUnderline          =  "\ESC[4m\STX"
setColour colourCode  =  "\ESC[3"++colourCode:"m\STX"

setStyle :: [Style] -> String
--setStyle  = concat . reverse . map showStyle
setStyle  = concat . map showStyle
reset = putStrLn resetStyle -- useful in GHCi to tidy up!
\end{code}


\section{Sized String Types}

\begin{eqnarray*}
  ss &::=& ss_{atom} \mid  ss_{ldelim} ~ ss_{delim} ~ ss_{sep} ~ ss^*
\end{eqnarray*}
We implement these using two mutually recursive datatypes where
the top level-one (\h{SS}) wraps the above structure with an integer that gives the
rendered length of the structure, at each level.
\begin{code}
data SS = SS Int SS' deriving (Eq,Ord,Show)

data SS' = SSA String          -- atom
         | SSS Style SS       -- style
         | SSC SS SS SS [SS]  -- rdelim ldelim sep sss
         deriving (Eq,Ord,Show)

-- useful query
sssize :: SS -> Int
sssize (SS s _) = s
\end{code}


\section{Smart Constructors}

We build smart versions of the \h{SSA}, \h{SSS} and \h{SSC}
constructors
that automatically accumulate the length information.
\begin{code}
ssa :: String -> SS
ssa str = SS (length str) $ SSA str

sss :: Style -> SS -> SS
sss style ss@(SS len _) = SS len $ SSS style ss

ssc :: SS -> SS -> SS -> [SS] -> SS
ssc lss rss seps sss
 = SS sslen $ SSC lss rss seps sss
 where
  sslen = sssize lss + sssize rss + sepsize sss * sssize seps
          + sum (map sssize sss)
  sepsize xs
   | len == 0  =  0
   | otherwise  =  len - 1
   where len = length xs
\end{code}

\newpage
A useful utility for putting (single) spacec around things (typically operators):
\begin{code}
pad :: String -> String
pad s = ' ':s++" "
\end{code}

We then provide some useful builders for common idioms,
mostly where delimiters and separators are atomic.
\begin{code}
ssnul :: SS -- the empty string
ssnul = ssa ""

ssopen' :: SS -> [SS] -> SS
ssopen' = ssc ssnul ssnul

ssopen :: String -> [SS] -> SS
ssopen sepstr sss = ssopen' (ssa sepstr) sss

sssopen :: Style -> String -> [SS] -> SS
sssopen style sepstr ppp = ssopen' (sss style $ ssa sepstr) ppp

sslist :: [SS] -> SS
sslist = ssopen ""

ssbracket :: String -> SS -> String -> SS
ssbracket lbr ss rbr = ssclosed lbr rbr "" [ss]

ssclosed :: String -> String -> String -> [SS] -> SS
ssclosed lstr rstr sepstr sss
  = ssc (ssa lstr) (ssa rstr) (ssa sepstr) sss
\end{code}
Code to add parentheses when required by a change in current precedence level.
This assumes that lower precedence values mean a looser binding,
so if the inner is looser than the outer we need to bracket it.
\begin{code}
paren :: Int -> Int -> SS -> SS
paren outerp innerp (SS w (SSC _ _ seps sss))
 | innerp < outerp  =  ssc (ssa "(") (ssa ")") seps sss
paren outerp innerp ss = ss
\end{code}


\newpage
\section{Simple Rendering}

It is useful to get the string produced
if a \h{SS} is all rendered on one line.
\begin{code}
ss2str :: [Style] -> SS -> String
ss2str stls (SS _ ss') = ss'2str stls ss'

ss'2str :: [Style] -> SS' -> String
ss'2str _ (SSA str) = str

ss'2str stls (SSS style ss)
 = concat [ showStyle style -- set new style style
          , ss2str (style:stls) ss -- recurse with styles updated
          , resetStyle -- clear all styles
          , setStyle stls -- restore current style
          ]

ss'2str stls (SSC lss rss seps [])
  =  ss2str stls lss ++ ss2str stls rss

ss'2str stls (SSC lss rss seps sss)
 | sssize lss == 0  =  pppps stls rss seps sss
 | otherwise        =  ss2str stls lss ++ pppps stls rss seps sss
 where

  pppps :: [Style] -> SS -> SS -> [SS] -> String
  pppps stls rss seps []        =  ss2str stls rss
  pppps stls rss seps [ss]      =  ss2str stls ss ++ ss2str stls rss
  pppps stls rss seps (ss:sss)
    =  ss2str stls ss ++ ss2str stls seps ++ pppps stls rss seps sss
\end{code}



\section{Full Rendering}

Now, rendering it as a `nice' string.
We provide the desired column width at the top level,
along with an specified initial indentation
or one set to zero.
\begin{code}
renderIn :: Int -> Int -> SS -> String
renderIn w0 ind = fmtShow . layout [] (w0-ind) ind

render :: Int -> SS -> String
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

\newpage
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
layout :: [Style] ->Int -> Int -> SS -> [SLayout]

-- handle style changes
layout ss w i (SS _ (SSS s ss')) = layout (s:ss) w i ss'

-- 1st three cases: cannot break, or can fit on line
layout ss _ i (SS _ (SSA str))          =  [(Txt str,ss)]
layout ss _ i ss'@(SS _ (SSC _ _ _ []))  =  [(Txt $ ss2str ss ss', ss)]
layout ss w i ss'@(SS s _)  | s <= w     =  [(Txt $ ss2str ss ss', ss)]

-- case when non-trivial comp and it is too wide
layout ss w i (SS _ (SSC lss rss seps sss))
 = layout' ss w i (w-s) (i+s) lss rss seps sss -- sss not null
 where s = max (sssize lss) (sssize seps)
\end{code}

\newpage
The helpers, \h{layout'} and \h{layout''}
need to track outer (\h{w i}) and inner (\h{w' i'}) values
of width and indentation.
\begin{code}
-- we need to split it up

-- singleton case:   lss \n pp \n rss
layout' ss w i w' i' lss rss seps [pp]
 = layout ss w i lss
   ++ (NL,ss) : (Ind i',ss) : layout ss w' i' pp
   ++ (NL,ss) : (Ind i, ss) : layout ss w i rss

-- general case
layout' ss w i w' i' lss@(SS lw _) rss seps (pp:sss)
 = (Txt $ ss2str ss lss, ss) : (Ind (i'-(i+lw)),ss) -- header line
                        : (layout ss w' i' pp)
   ++
   (NL,ss) : layout'' ss w i w' i' rss seps sss -- sss not null

layout'' ss w i w' i' rss@(SS rw _) seps@(SS sw _) [pp]
 = (Ind i,ss) : (Txt $ ss2str ss seps, ss)
                    : (Ind (i'-(i+sw)),ss) : layout ss w' i' pp
   ++ [(Txt $ ss2str ss rss,ss)]

layout'' ss w i w' i' rss seps@(SS sw _) (pp:sss)
 = (Ind i,ss) : (Txt $ ss2str ss seps, ss)
                    : (Ind (i'-(i+sw)),ss) : layout ss w' i' pp
   ++
   (NL,ss) : layout'' ss w i w' i' rss seps sss -- sss not null
\end{code}
