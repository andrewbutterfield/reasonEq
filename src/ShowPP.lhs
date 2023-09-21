\section{Show Pretty-Print}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.Environment
import System.IO
import Data.List
import Data.Char

import Utilities
\end{code}

\subsection{Finding ``Show'' lines}

We can run utility as a standalone application
that takes a file containing failing tests,
and debug output generated using \texttt{show},
and pretty-prints them to make debugging easier.

Form of a test fail:
\begin{verbatim}
  <test description>: [Failed]
expected: <Haskell Show Output>
 but got: <Haskell Show Output>
\end{verbatim}
Show lines marked by hand:
\begin{verbatim}
--<comment>
@<descr>
<Haskell Show Output>
\end{verbatim}
\begin{code}
failPost  = ": [Failed]" ; fpfLen = length failPost
expPre    = "expected: " ; epfLen = length expPre
gotPre    = " but got: " ; bpfLen = length gotPre
handPre   = "@"          ; byhLen = length handPre
cmtPre    = "--"         ; cmtLen = length cmtPre
\end{code}


A simple check for a failure line:
\begin{code}
isFailed ln   =  deliafPreFix `isPrefixOf` reverse ln
deliafPreFix  =  reverse failPost
\end{code}

A check for a GHCi prompt line:
\begin{code}
isGHCiPrompt ln
 = checkAst ln
 where
    checkAst ('*':cs) = skipModName cs
    checkAst _ = False
    skipModName ('>':_) = True
    skipModName (c:cs)
      | isAlpha c || isDigit c || c == '_'  = skipModName cs
    skipModName _ = False
\end{code}


\newpage
\subsection{Prettifying Show Lines}

We scan lines, skipping until we find one that has the ``Failed'' postfix,
or one of a number of designated prefixes:
``expected'', ``but got'', and ``@''.
In each case we remove the prefix and output on a line by itself.
We then pretty-print the rest of the line.

\begin{code}
ppFails []  =  []
ppFails (ln:lns)
-- | isGHCiPrompt ln            =  ln : ppNext lns
-- really need a GHCi 'mode'
-- what we have here is a stack test 'mode'
 | isFailed ln                =  "" : ln : ppFails lns
 | take cmtLen ln == cmtPre   =  ln : ppFails lns
 | take byhLen ln == handPre  =  ln : ppNext lns
 | take epfLen ln == expPre   =  expPre : (pp $ drop epfLen ln) : ppFails lns
 | take bpfLen ln == gotPre   =  gotPre : (pp $ drop bpfLen ln) : ppFails lns
 | otherwise                  =  ppFails lns

ppNext [] = []
ppNext (ln:lns) = pp ln : ppFails lns
\end{code}


\subsection{Show Pretty Main}

This should be run from the repo top-level and looks
for input from \texttt{stdin}
and produces output to \texttt{stdout}.

To compile enter the \texttt{/src} directory
and do:
\begin{verbatim}
ghc -o showpp ShowPP.lhs
\end{verbatim}
Then move \texttt{showpp} to somewhere on your \verb"$PATH".
\begin{code}
doShowPP
 = do txt <- hGetContents stdin
      let lns = lines txt
      let lnspp = ppFails lns
      hPutStr stdout $ unlines lnspp
\end{code}

\begin{code}
main
  = do args <- getArgs
       processArgs args

processArgs [] = doShowPP
processArgs _
  =  putStrLn $ unlines
       [ "Usage: "
       , "    showpp < rawfile > ppfile"
       , "    rawprog | showp > ppfile"
       , " showp reads stdin, writes stdout"
       ]
\end{code}
