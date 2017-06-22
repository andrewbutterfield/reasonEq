\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import AST

version = "0.1.0.0"
main :: IO ()
main
  = do putStrLn ("\n\tWelcome to reasonEq "++version++"\n")
       putStrLn ("AST.vscTrue = "++show vscTrue)
       putStrLn ("AST.scTrue  = "++show scTrue)
       putStrLn "\n\tGoodbye."
\end{code}
