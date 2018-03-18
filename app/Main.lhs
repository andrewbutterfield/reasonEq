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

summariseREqS reqs = '.':show reqs
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
   minput <- getInputLine ("REq"++summariseREqS reqs++"- ")
   case minput of
       Nothing -> outputStrLn "Input Stop"
       Just "quit" -> outputStrLn "Goodbye!"
       Just input -> docommand reqs (words input) >>= loop
\end{code}

REPL Commands:
\begin{code}
type Command = [String] -> REqState -> InputT IO REqState
type CommDescr = ( String     -- command name
                 , String     -- short help for this command
                 , String     -- long help for this command
                 , Command )  -- command function
type Commands = [CommDescr]

clookup _ []  =  Nothing
clookup s (cd@(n,_,_,_):rest)
 | s == n     =  Just cd
 | otherwise  =  clookup s rest

docommand reqs [] = return reqs
docommand reqs ("?":what)
 = help reqs what
docommand reqs (cmd:args)
 = case clookup cmd commands of
     Nothing -> outputStrLn ("unknown cmd: '"++cmd++"'") >> return reqs
     Just (_,_,_,c)  ->  c args reqs

help reqs []
  = do outputStrLn "Commands:"
       outputStrLn "?     -- this help message"
       outputStrLn "? cmd -- help for 'cmd'"
       outputStrLn "quit  -- exit program."
       outputStrLn $ unlines $ map shorthelp commands
       return reqs
  where shorthelp (cmd,sh,_,_) = cmd ++ "  -- " ++ sh

help reqs (what:_)
  = case clookup what commands of
     Nothing -> outputStrLn ("unknown cmd: '"++what++"'") >> return reqs
     Just (_,_,lh,_) -> outputStrLn lh >> return reqs


commands :: [CommDescr]
commands = [("X","'x'","the msyterious 'X' !",xcomm)]

xcomm _ reqs = outputStrLn "X! Whoo! X!" >> return (reqs+1)
\end{code}
