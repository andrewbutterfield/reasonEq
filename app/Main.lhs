\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.Environment
import System.Console.Haskeline
import Control.Monad.IO.Class
import Data.Map (Map)
import qualified Data.Map as M

import Data.List
\end{code}

\begin{code}
name = "reasonEq"
version = "0.5.0.0++"
\end{code}

\subsubsection{Top Level Code}
\begin{code}
main :: IO ()
main
  = do args <- getArgs
       if "-g" `elem` args
       then gui (args \\ ["-g"])
       else repl args
\end{code}

\newpage
\subsubsection{System State}
\begin{code}
type REqState = Int

initState :: [String] -> IO REqState
initState args = return (42+1000000*length args)
\end{code}


\newpage
\subsubsection{GUI Top-Level}
\begin{code}
gui :: [String] -> IO ()
gui args = putStrLn $ unlines
         [ "Welcome to "++name++" "++version
         , "GUI N.Y.I.!"
         , "Goodbye" ]
\end{code}

\newpage
\subsubsection{REPL Top-Level}
\begin{code}
repl :: [String] -> IO ()
repl args = runInputT defaultSettings
                                 (banner >> (liftIO $ initState args) >>= loop)
banner :: InputT IO ()
banner = outputStrLn $ unlines
 [ "Welcome to the "++name++" "++version++" REPL"
 ]

loop :: REqState -> InputT IO ()
loop reqs = do
   minput <- getInputLine ("reasonEq["++show reqs++"]- ")
   case minput of
       Nothing -> outputStrLn "Input Failure"
       Just "quit" -> outputStrLn "Goodbye!"
       Just input -> docommand reqs input >>= loop
\end{code}

REPL Commands:
\begin{code}
type Command = [String] -> InputT IO REqState
type Commands = Map String (Command, String, String)

docommand reqs "?"
 = outputStrLn "help not yet done" >> return reqs
docommand reqs cmd
 = outputStrLn (cmd ++ " not yet done") >> return reqs
\end{code}
