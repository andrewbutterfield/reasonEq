\chapter{Debug Support}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2023-25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Debugger
 ( dbg, pdbg, pdbn, mdbg, rdbg, rdbn, ldbg, fdbg, trc ) 
where

import Debug.Trace

import YesBut
\end{code}

We extend \texttt{Debug.trace} in a number of ways.

First, 
showing the 2nd argument of a trace 
after displaying the 1st argument string:
\begin{code}
type Dbg a  = String -> a -> a
dbg :: Show a => Dbg a
dbg msg x = trace (msg++show x) x
\end{code}

Secondly, marking output (with \texttt{@}) and optionally starting a newline:
\begin{code}
pdbg, pdbn :: Show a => Dbg a
pdbg nm x = dbg ('@':nm++":  ") x
pdbn nm x = dbg ('@':nm++":\n") x
\end{code}

Next, a version to handle monadic-fail types,
that coerces them to \texttt{YesBut} so we can observe either outcome,
before returning them back to their more general monadic state:
\begin{code}
mdbg :: (Show a, MonadFail m) => [Char] -> YesBut a -> m a
mdbg nm mx
  = case mx of 
     Yes y     ->  return $ pdbg nm y
     But msgs  ->  fail $ pdbg nm (unlines msgs)
\end{code}

Now, versions of \h{pdbg} where a rendering function is supplied, 
rather than using \h{show}, and where the newline is optional.
\begin{code}
rdbg, rdbn :: (a -> String) -> Dbg a
rdbg render nm x = trace ('@':nm++":  "++render x) x
rdbn render nm x = trace ('@':nm++":\n"++render x) x
\end{code}

Being able to show aggregates is helpful. Let's start with lists:
\begin{code}
type Dbgs a = String -> [a] -> [a]
ldbg :: (a -> String) -> Dbgs a
ldbg render nm xs = trace ('@':nm++":\n"++dbgs render xs) xs

dbgs :: (a -> String) -> [a] -> String
dbgs render xs = unlns' $ map (("  "++) . render) xs
\end{code}

Finally, a short-name version of \texttt{trace} for local customisations:
\begin{code}
trc :: Show a => Dbg a
trc = trace 
\end{code}

What about?
\begin{code}
fdbg f nm x  =  trace ('@':nm++":\n"++show (f x)) x
\end{code}


We have a debugging version of `h{unlines'}` here,
so that \h{Utilities} can use debug features.
\begin{code}
unlns' [] = ""
unlns' [s] = s
unlns' (s:ss) = s ++ '\n':unlns' ss
\end{code}
