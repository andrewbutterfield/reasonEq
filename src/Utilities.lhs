\section{Utilities}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Utilities
where

import Data.List
import Data.Char
import Data.Set(Set)
import qualified Data.Set as S
\end{code}

Here we provide odds and ends not found elswhere.

\begin{code}
utilities
 = do putStrLn "Useful interactive Utilities"
      putStrLn " putShow :: Show t =>      t -> IO ()"
      putStrLn " putPP   ::           String -> IO ()"
\end{code}

\newpage
\subsubsection{Maybe and related}

A version of \texttt{fromJust}
that gives a more helpful error message.
\begin{code}
getJust :: String -> Maybe t -> t
getJust _   (Just x)  =  x
getJust msg Nothing   =  error msg
\end{code}

\newpage
\subsection{List and Set Functions}

\subsubsection{Predicate: has duplicates}
\begin{code}
hasdup :: Eq a => [a] -> Bool
hasdup xs = xs /= nub xs
\end{code}

\subsubsection{Pulling Prefix from a List}
\begin{code}
pulledFrom :: Eq a => [a] -> [a] -> (Bool, [a])
[]     `pulledFrom` ys  =  (True, ys)
xs     `pulledFrom` []  =  (False,[])
(x:xs) `pulledFrom` (y:ys)
 | x == y     =  xs `pulledFrom` ys
 | otherwise  =  (False,ys)
\end{code}

\subsubsection{Un-lining without a trailing newline}
\begin{code}
unlines' [] = ""
unlines' [s] = s
unlines' (s:ss) = s ++ '\n':unlines' ss
\end{code}

\subsubsection{Get item from list, or fail trying}
\begin{code}
getitem :: (Eq a, Monad m) => a -> [a] -> m [a]
getitem _ [] = fail "getitem: item not present"
getitem a (x:xs)
 | a == x     =  return xs
 | otherwise  =  do xs' <- getitem a xs
                    return (x:xs')
\end{code}

\subsubsection{Intercalation, dropping nulls}
\begin{code}
intcalNN sep = intercalate sep . filter (not . null)
\end{code}

\subsubsection{Set disjointness}

\begin{code}
disjoint, overlaps :: Ord a => Set a -> Set a -> Bool
s1 `disjoint` s2 = S.null (s1 `S.intersection` s2)
\end{code}

\subsubsection{Set overlap}

\begin{code}
s1 `overlaps` s2 = not (s1 `disjoint` s2)
\end{code}

\subsubsection{Choosing element from a set}

\begin{code}
choose s
 | S.null s  =  error "choose: empty set."
 | otherwise  = (x,s')
 where
   x = S.elemAt 0 s
   s' = S.delete x s
\end{code}

\newpage
\subsection{Smart Readers}

\subsubsection{Read Integer}
\begin{code}
readInt :: String -> Int
readInt str
 | all isDigit str  =   read str
 | otherwise        =   -1
\end{code}
\newpage
\subsection{Control-Flow Functions}

\subsubsection{Repeat Until Equal}

\begin{code}
untilEq :: Eq a => (a -> a) -> a -> a
untilEq f x
 | x' == x  =  x
 | otherwise  =  untilEq f x'
 where x' = f x
\end{code}

\newpage
\subsection{Pretty-printing Derived Show}

A utility that parses the output of \texttt{derived} instances of \texttt{show}
to make debugging easier.

\begin{code}
putShow :: Show t => t -> IO ()
putShow = putPP . show

putPP :: String -> IO ()
putPP = putStrLn . pp

pp :: String -> String
--pp = display0 . pShowTree . lexify
--pp = display1 . showP
pp = display2 . showP

showP :: String -> ShowTree
showP = pShowTree . lexify
\end{code}

Basically we look for brackets (\texttt{[]()}) and punctuation (\texttt{,})
and build a tree.

\subsubsection{Pretty-printing Tokens}

Tokens are the five bracketing and punctuation symbols above,
plus any remaining contiguous runs of non-whitespace characters.
\begin{code}
data ShowTreeTok
 = LSqr | RSqr | LPar | RPar | Comma | Run String
 deriving (Eq, Show)

lexify :: String -> [ShowTreeTok]
lexify "" = []
lexify (c:cs)
 | c == '['   =  LSqr  : lexify cs
 | c == ']'   =  RSqr  : lexify cs
 | c == '('   =  LPar  : lexify cs
 | c == ')'   =  RPar  : lexify cs
 | c == ','   =  Comma : lexify cs
 | isSpace c  =  lexify cs
 | otherwise  =  lex' [c] cs

lex' nekot "" = [rrun nekot]
lex' nekot (c:cs)
 | c == '['   =  rrun nekot : LSqr  : lexify cs
 | c == ']'   =  rrun nekot : RSqr  : lexify cs
 | c == '('   =  rrun nekot : LPar  : lexify cs
 | c == ')'   =  rrun nekot : RPar  : lexify cs
 | c == ','   =  rrun nekot : Comma : lexify cs
 | isSpace c  =  rrun nekot         : lexify cs
 | otherwise  =  lex' (c:nekot) cs

rrun nekot = Run $ reverse nekot

spaced s = ' ':s ++ " "
\end{code}

\newpage
\subsubsection{Parsing Tokens}

We parse into a ``Show-Tree''
\begin{code}
data ShowTree
 = STtext String     -- e.g.,  D "m" 5.3 1e-99
 | STapp [ShowTree]  -- e.g., Id "x"
 | STlist [ShowTree]
 | STpair [ShowTree]
 deriving (Eq, Show)
\end{code}

The parser
\begin{code}
pShowTree :: [ShowTreeTok] -> ShowTree
pShowTree toks
 = case pContents [] [] toks of
     Nothing  ->  STtext "?"
     Just (contents,[])  ->  wrapContents stapp contents
     Just (contents,_ )  ->  STpair [wrapContents stapp contents,STtext "??"]
\end{code}

Here we accumulate lists within lists.
Internal list contents are sperated by (imaginary) whitespace,
while external lists have internal lists as components,
separated by commas.
\begin{code}
pContents :: Monad m
          => [[ShowTree]] -- completed internal lists
          -> [ShowTree]   -- internal list currently under construction
          -> [ShowTreeTok] -> m ([[ShowTree]], [ShowTreeTok])

-- no tokens left
pContents pairs []  [] = return (reverse pairs, [])
pContents pairs app [] = return (reverse (reverse app:pairs), [])

-- ',' starts a new internal list
pContents pairs app (Comma:toks)  =  pContents (reverse app:pairs) [] toks

-- a run is just added onto internal list being built.
pContents pairs app (Run s:toks)  =  pContents pairs (STtext s:app) toks

-- '[' triggers a deep dive, to be terminated by a ']'
pContents pairs app (LSqr:toks)
 =  do (st,toks') <- pContainer STlist RSqr toks
       pContents pairs (st:app) toks'
pContents pairs app toks@(RSqr:_)
 | null app   =  return (reverse pairs, toks)
 | otherwise  =  return (reverse (reverse app:pairs), toks)

-- '(' triggers a deep dive, to be terminated by a ')'
pContents pairs app (LPar:toks)
 =  do (st,toks') <- pContainer STpair RPar toks
       pContents pairs (st:app) toks'
pContents pairs app toks@(RPar:_)
 | null app   =  return (reverse pairs, toks)
 | otherwise  =  return (reverse (reverse app:pairs), toks)
\end{code}

\newpage
A recursive dive for a bracketed construct:
\begin{code}
pContainer :: Monad m
           => ([ShowTree] -> ShowTree) -- STapp, STlist, or STpair
           -> ShowTreeTok              -- terminator, RSqr, or RPar
           -> [ShowTreeTok] -> m (ShowTree, [ShowTreeTok])

pContainer cons term toks
 = do (contents,toks') <- pContents [] [] toks
      if null toks' then fail "container end missing"
      else if head toks' == term
           then return (wrapContents cons contents, tail toks')
           else tfail toks' "bad container end"
\end{code}

Building the final result:
\begin{code}
--wrapContents cons [[st]] = st
wrapContents cons contents = cons $ map stapp contents
\end{code}

Avoiding too many nested uses of \texttt{STapp},
and complain if any are empty.
A consequence of this is that all \texttt{STapp}
will have length greater than one.
\begin{code}
stapp [] = error "stapp: empty application!"
stapp [STapp sts] = stapp sts
stapp [st] = st
stapp sts = STapp sts
\end{code}

Informative error:
\begin{code}
tfail toks str = fail $ unlines [str,"Remaining tokens = " ++ show toks]
\end{code}

\subsubsection{Displaying Show-Trees}

Heuristic Zero: all on one line:
\begin{code}
display0 :: ShowTree -> String
display0 (STtext s)    =  s
display0 (STapp sts)   =  intercalate " " $ map display0 sts
display0 (STlist sts)  =  "[" ++ (intercalate ", " $ map display0 sts) ++"]"
display0 (STpair sts)  =  "(" ++ (intercalate ", " $ map display0 sts) ++")"
\end{code}

Heuristic One: Each run on a new line, with indentation.
\begin{code}
display1 :: ShowTree -> String
display1 st = disp1 0 st

disp1 _ (STtext s) = s
disp1 i (STapp (st:sts)) -- length always >=2, see stapp above,
  = disp1 i st ++  '\n' : (unlines' $ map ((ind i ++) . disp1 i) sts)
disp1 i (STlist []) = "[]"
disp1 i (STlist (st:sts)) = "[ "++ disp1 (i+2) st ++ disp1c i sts ++ " ]"
disp1 i (STpair (st:sts)) = "( "++ disp1 (i+2) st ++ disp1c i sts ++ " )"

disp1c i [] = ""
disp1c i (st:sts) = "\n" ++ ind i ++ ", " ++  disp1 (i+2) st ++ disp1c i sts

ind i = replicate i ' '
\end{code}

\newpage
Heuristic 2:  designated text values at start of \texttt{STapp}
mean it is inlined as per Heuristic Zero.
\begin{code}
display2 :: ShowTree -> String
display2 st = disp2 0 st

inlineKeys = map STtext
  ["BV","BT","E","K","VB","VI","VT","V","GL","GV","LV","VR","Id","WD"]

disp2 _ (STtext s) = s
disp2 i app@(STapp (st:sts)) -- length always >=2, see stapp above,
 | st `elem` inlineKeys  = display0 app
 | otherwise = disp2 i st ++  '\n' : (unlines' $ map ((ind i ++) . disp2 i) sts)
disp2 i (STlist []) = "[]"
disp2 i (STlist (st:sts)) = "[ "++ disp2 (i+2) st ++ disp2c i sts ++ " ]"
disp2 i (STpair []) = "()"
disp2 i (STpair (st:sts)) = "( "++ disp2 (i+2) st ++ disp2c i sts ++ " )"

disp2c i [] = ""
disp2c i (st:sts) = "\n" ++ ind i ++ ", " ++  disp2 (i+2) st ++ disp2c i sts
\end{code}



\newpage
\subsection{Possible Failure Monad}

\subsubsection{Datatype: Yes, But \dots}

\begin{code}
data YesBut t
 = Yes t
 | But [String]
 deriving (Eq,Show)
\end{code}

\subsubsection{Instances: Functor, Applicative, Monad}

\begin{code}
instance Functor YesBut where
  fmap f (Yes x)    =  Yes $ f x
  fmap f (But msgs)  =  But msgs

instance Applicative YesBut where
  pure x = Yes x

  Yes f <*> Yes x          =  Yes $ f x
  Yes f <*> But msgs       =  But msgs
  But msgs1 <*> But msgs2  =  But (msgs1++msgs2)

instance Monad YesBut where
  Yes x   >>= f   =  f x
  But msgs >>= f   =  But msgs

  fail msg        =  But [msg]
\end{code}
