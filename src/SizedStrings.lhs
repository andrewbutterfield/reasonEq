\chapter{Sized String Structures}
\begin{code}
module SizedStrings
 ( Style(..)
 , styleRed, styleMagenta
 , showStyle
 , resetStyle, setUnderline, setColour
 , setStyle
 , SS(..), sssize
 , ssa,sss,ssw,ssl,sso
 , ssc, pad
 , ssnul,ssopen,sslist,ssclosed
 , paren
 , ss2str
 , fuseSS
 -- , renderIn,render 
 )
where
import Utilities
import Data.List
\end{code}

Our pretty printer handles atomic pieces, which render as is,
and composite parts, defined as a list of parts, along with descriptions
of the left and right delimiters and a separator part.
Composites will be rendered with line breaks and indentation
in a manner that is hopefully maximally pleasing.
We also provide a (simple) means for applying character ``styles''
(colour,weight,underlining,\dots).

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



We implement these using a recursive datatype with an integer that gives the
rendered length of the structure, at each level.
The length is set correctly by using builders provided below:
\begin{code}
data SS = SSA Int String    -- atom
        | SSS Int Style SS  -- style             - zero width appearance 
        | SSW Int SS SS SS  -- ldelim rdelim ss  - bracketing
        | SSL Int SS [SS]   -- sep sss           - list with separator
        | SSO Int SS [SS]   -- inop sss          - infix ops
        deriving (Eq,Ord,Show)

-- useful query
sssize :: SS -> Int
sssize (SSA s _)      =  s
sssize (SSS s _ _)    =  s
sssize (SSW s _ _ _)  =  s
sssize (SSL s _ _)    =  s
sssize (SSO s _ _)    =  s

-- the "unit of compostion"
ssnul = (SSA 0 "")
\end{code}

\newpage
\section{Smart Constructors}

We build smart versions of the 
\h{SSA}, \h{SSS}, \h{SSW},\h{SSCL}, and \h{SSO} constructors
that automatically accumulate the length information.
\begin{code}
ssa :: String -> SS
ssa str = SSA (length str) str

sss :: Style -> SS -> SS
sss style ss  = SSS (sssize ss) style ss

ssw :: SS -> SS -> SS -> SS
ssw lss rss ss = SSW (sssize lss+sssize rss+sssize ss) lss rss ss

ssl :: SS -> [SS] -> SS
ssl sep []    =  ssnul
ssl sep [ss]  =  ss
ssl sep sss   =  mkcomp SSL sep sss

sso :: SS -> [SS] -> SS
sso sep []    =  ssnul
sso sep [ss]  =  ss
sso sep sss   =  mkcomp SSO sep sss

mkcomp :: (Int -> SS -> [SS] -> SS) -> SS -> [SS] -> SS
mkcomp cons sep sss = cons sslen sep sss
 where
  sslen = sepsize sss * sssize sep + sum (map sssize sss)
  sepsize xs
   | len == 0  =  0
   | otherwise  =  len - 1
   where len = length xs

-- backwards compatibiliy
ssc ldelim rdelim sep sss = ssw ldelim rdelim $ ssl sep sss
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
ssopen :: String -> [SS] -> SS
ssopen sepstr sss = ssl (ssa sepstr) sss

sslist :: [SS] -> SS
sslist = ssopen ""

ssbracket :: String -> SS -> String -> SS
ssbracket lbr ss rbr = ssw (ssa lbr) (ssa rbr) ss

ssclosed :: String -> String -> String -> [SS] -> SS
ssclosed lstr rstr sepstr sss
  = ssc (ssa lstr) (ssa rstr) (ssa sepstr) sss
\end{code}
Code to add parentheses when required by a change in current precedence level.
This assumes that lower precedence values mean a looser binding,
so if the inner is looser than the outer we need to bracket it.
\begin{code}
paren :: Int -> Int -> SS -> SS
paren outerp innerp ss@(SSL _ _ _)
 | innerp < outerp  =  ssw (ssa "(") (ssa ")") ss
paren outerp innerp ss@(SSO _ _ _)
 | innerp < outerp  =  ssw (ssa "(") (ssa ")") ss
paren outerp innerp ss = ss
\end{code}


\newpage
\section{Simple Rendering}

It is useful to get the string produced
if a \h{SS} is all rendered on one line.
\begin{code}
ss2str :: [Style] -> SS -> String
ss2str _ (SSA _ str) = str


ss2str stls (SSS _ style ss)
 = concat [ showStyle style -- set new style style
          , ss2str (style:stls) ss -- recurse with styles updated
          , resetStyle -- clear all styles
          , setStyle stls -- restore current style
          ]

ss2str stls (SSW _ ldelim rdelim ss)
  =  ss2str stls ldelim ++ ss2str stls ss ++ ss2str stls rdelim

ss2str stls (SSL _ _ [])   =  ""
ss2str stls (SSL _ sep sss)  =  pppps stls sep sss

ss2str stls (SSO _ _ [])  =  ""
ss2str stls (SSO _ op sss)  = pppps stls op sss

pppps :: [Style] -> SS -> [SS] -> String
pppps stls  sep []        =  []
pppps stls  sep [ss]      =  ss2str stls ss 
pppps stls  sep (ss:sss)
    =  ss2str stls ss ++ ss2str stls sep ++ pppps stls sep sss
\end{code}

\section{Fusing}

Sometimes it can be useful to take two \h{SS} and fuse them together
for make a single \h{SS}.
We fuse \h{SS w1 ss1'} and \h{SS w2 ss2'} 
to get \h{SS w1+w2 ss'?}.
\begin{code}
fuseSS :: SS -> SS -> SS
\end{code}
If both are instances of \h{SSA}, 
or instances of \h{SSS},this is straightforward:
\begin{code}
fuseSS (SSA w1 s1) (SSA w2 s2) = SSA (w1+w2) (s1++s2)
\end{code}
For now, anything else gets put inside a \h{SSL}:
\begin{code}
fuseSS ss1 ss2  = SSL (sssize ss1+sssize ss2) ssnul [ss1,ss2]
\end{code}


% \section{Full Rendering}

% \textbf{This is really pretty-printing which is probably better done by the client}

% Now, rendering it as a `nice' string.
% We provide the desired column width at the top level,
% along with an specified initial indentation
% or one set to zero.
% \begin{code}
% renderIn :: Int -> Int -> SS -> String
% renderIn w0 ind = fmtShow . layout [] (w0-ind) ind

% render :: Int -> SS -> String
% render w0 = renderIn w0 0
% \end{code}

% \subsection{Lines and Formatting}

% We have atomic strings present,
% and we also need to explicitly identify newlines and indents.
% All of these need to have an associated style.
% \begin{code}
% data Layout = NL | Ind Int | Txt String deriving Show

% type SLayout = (Layout,[Style])
% \end{code}

% \newpage
% We obtain the final string by merging \h{Fmt} with \h{Txt} on either
% side before calling \h{unlines}
% (otherwise formatting commands introduce spurious linebreaks).
% \begin{code}
% lstr NL         =  "\n"
% lstr (Ind i)    =  ind i ""
% lstr (Txt str)  =  str

% fmtShow :: [SLayout] -> String
% fmtShow = concat . fshow []
%  where
%    fshow [] [] = []
%    fshow _  [] = [resetStyle]
%    fshow ss ((layout,ss'):slayouts)
%     | ss == ss'  =  lstr layout :  fshow ss' slayouts
%     | otherwise
%        = resetStyle : setStyle ss' : lstr layout : fshow ss' slayouts
% \end{code}

% \paragraph{List viewer}

% Show list elements one per line:
% \begin{code}
% ldisp :: Show a => [a] -> IO ()
% ldisp = putStrLn . unlines' . map show
% \end{code}


% \subsection{Layout}

% The main recursive layout algorithm has a width and indentation parameter
% ---
% the sum of these is always constant.
% \begin{code}
% -- w+i is constant;  w+i=w0 above
% layout :: [Style] ->Int -> Int -> SS -> [SLayout]

% -- handle style changes
% layout stls w i (SSS _ s ss') = layout (s:ss) w i 

% -- 1st three cases: cannot break, or can fit on line
% layout ss _ i (SSA _ str))         =  [(Txt str,ss)]
% layout ss _ i ss'@(SSC _ _ _ _ [])  =  [(Txt $ ss2str i ss ss', ss)]
% layout ss w i ss'@(SS s _)  | s <= w     =  [(Txt $ ss2str i ss ss', ss)]

% -- case when non-trivial comp and it is too wide
% layout ss w i (SS _ (SSC lss rss seps sss))
%  = layout' ss w i (w-s) (i+s) lss rss seps sss -- sss not null
%  where s = max (sssize lss) (sssize seps)
% \end{code}

% \newpage
% The helpers, \h{layout'} and \h{layout''}
% need to track outer (\h{w i}) and inner (\h{w' i'}) values
% of width and indentation.
% \begin{code}
% -- we need to split it up

% -- singleton case:   lss \n pp \n rss
% layout' ss w i w' i' lss rss seps [pp]
%  = layout ss w i lss
%    ++ (NL,ss) : (Ind i',ss) : layout ss w' i' pp
%    ++ (NL,ss) : (Ind i, ss) : layout ss w i rss

% -- general case
% layout' ss w i w' i' lss@(SS lw _) rss seps (pp:sss)
%  = (Txt $ ss2str i ss lss, ss) : (Ind (i'-(i+lw)),ss) -- header line
%                         : (layout ss w' i' pp)
%    ++
%    (NL,ss) : layout'' ss w i w' i' rss seps sss -- sss not null

% layout'' ss w i w' i' rss@(SS rw _) seps@(SS sw _) [pp]
%  = (Ind i,ss) : (Txt $ ss2str 0 ss seps, ss)
%                     : (Ind (i'-(i+sw)),ss) : layout ss w' i' pp
%    ++ [(Txt $ ss2str i ss rss,ss)]

% layout'' ss w i w' i' rss seps@(SS sw _) (pp:sss)
%  = (Ind i,ss) : (Txt $ ss2str 0 ss seps, ss)
%                     : (Ind (i'-(i+sw)),ss) : layout ss w' i' pp
%    ++
%    (NL,ss) : layout'' ss w i w' i' rss seps sss -- sss not null
% \end{code}

\subsection{Sized String Tests}

The following tests are intended to be run from within GHCi.

\begin{code}
addss = ssa "+"
addmrg n = ssa $ show n
addnums n = ssc ssnul ssnul addss $ take n $ map addmrg [1..] 
\end{code}