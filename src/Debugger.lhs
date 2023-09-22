\section{Debug Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 20232

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Debugger
 ( dbg, pdbg, mdbg ) 
where

import Debug.Trace

import Utilities
\end{code}

We extend \texttt{Debug.trace} in a number of ways.

First, 
showing the 2nd argument of a trace 
after displaying the 1st argument string:
\begin{code}
dbg :: Show a => [Char] -> a -> a
dbg msg x = trace (msg++show x) x
\end{code}

Secondly, marking output (with \texttt{@}) and starting a newline:
\begin{code}
pdbg :: Show a => [Char] -> a -> a
pdbg nm x = dbg ('@':nm++":\n") x
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