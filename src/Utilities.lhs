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
\end{code}

Here we provide odds and ends not found elswhere.

\subsection{List Functions}

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

\subsection{Control-Flow Functions}

\subsubsection{Repeat Until Equal}

\begin{code}
untilEq :: Eq a => (a -> a) -> a -> a
untilEq f x
 | x' == x  =  x
 | otherwise  =  untilEq f x'
 where x' = f x
\end{code}

\subsection{Pretty-printing Derived Show}

A utility that parses the output of \texttt{derived} instances of \texttt{show}
to make debugging easier.

\begin{code}
ppshow :: Show t => t -> IO ()
ppshow = putStrLn . pp . show

pp :: String -> String
pp = show . lexify
\end{code}

Basically we look for brackets (\texttt{[]()}) and punctuation (\texttt{,})
and build a tree.

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
\end{code}

We parse into a ``Show-Tree''
\begin{code}
data ShowTree
 = STtext String     -- e.g.,  D "m" 5.3 1e-99
 | STapp [ShowTree]  -- e.g., Id "x"
 | STlist [ShowTree]
 | STpair [ShowTree]
 deriving Show
\end{code}

The parser
\begin{code}
pShowTree :: Monad m => [ShowTreeTok] -> m (ShowTree, [ShowTreeTok])
pShowTree []     = fail "no tokens"
pShowTree (LSqr:toks) = pContainer STlist RSqr toks
pShowTree (LPar:toks) = pContainer STpair RPar toks
pShowTree (Run s:toks)
  = do (contents,toks') <- pContents [] [STtext s] toks
       return (wrapContents stapp contents, toks')
pShowTree toks = tfail toks "invalid start token"

pContainer cons term toks
 = do (contents,toks') <- pContents [] [] toks
      if null toks' then fail "container end missing"
      else if head toks' == term
           then return (wrapContents cons contents, tail toks')
           else fail "bad container end"

pContents pairs []  [] = return (reverse pairs, [])
pContents pairs app [] = return (reverse (reverse app:pairs), [])
pContents pairs app toks@(RSqr:_)  = return (reverse (reverse app:pairs), toks)
pContents pairs app toks@(RPar:_)  = return (reverse (reverse app:pairs), toks)
pContents pairs app (Comma:toks)  =  pContents (reverse app:pairs) [] toks
pContents pairs app toks
 = do (st,toks') <- pShowTree toks
      if null toks' then return (reverse ((reverse (st:app)):pairs), [])
      else if head toks' == Comma
           then pContents (reverse (st:app):pairs) [] $ tail toks'
           else pContents pairs (st:app) toks'

wrapContents cons [[st]] = st
wrapContents cons contents = cons $ map stapp contents

stapp [STapp sts] = stapp sts
stapp [st] = st
stapp sts = STapp sts

tfail toks str = fail $ unlines [str,"Remaining tokens = " ++ show toks]
\end{code}



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
