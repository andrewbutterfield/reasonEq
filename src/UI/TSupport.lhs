\chapter{TUI Support}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.TSupport
  ( selectByNumber
  , errorPause
  ) 
where
import System.IO

import Utilities
import UI.REPL (userPause)

import Debugger
\end{code}


\section{Description}

This module provides useful functions to support 
the Terminal User Interfaces (TUI).

\section{Error Reporting}

Sometimes we want to show an error before refreshing things:
\begin{code}
errorPause msgs state = do
  putStrLn $ unlines' msgs
  userPause
  return state
\end{code}

\section{Selecting from a List}

The general behavior we want is:
\begin{itemize}
  \item If the list is empty, report an error
  \item If the list is a singleton, automatically pick it.
    \newline (Some situations we may show it so the user has an opportunity to decline)
  \item Otherwise, display the list, and request the user to choose.
\end{itemize}

\subsection{List Selection by Number}

Items are always numbered from 1 upwards. 
The user can then reliably use zero to decline the offer.

\begin{code}
selectByNumber :: MonadFail m => (a -> String) -> [a] -> IO (m a)
selectByNumber print [] =  return $ fail "no items for selection"
selectByNumber print [x] = return $ return x
selectByNumber print xs = do
  let menu = numberList print xs
  putStrLn menu
  putStr "Select by number: "
  hFlush stdout
  choice <- getLine
  let ix = readNat choice
  if ix >= 1 && ix <= length xs
  then return $ return (xs!!(ix-1))
  else return $ fail "invalid selection"


test :: Show a => String -> [a] -> IO ()
test what xs = do
  m <- selectByNumber show xs
  display what m

display what Nothing = putStrLn (what++" NO")
display what (Just x) = putStrLn (what++" "++show x)
\end{code}