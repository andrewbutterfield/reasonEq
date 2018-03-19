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

import NiceSymbols hiding (help)
import AST
import VarData
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

Currently in prototyping mode,
so this is one large record.
Later we will nest things.
In order to support nested records properly,
for every record field \texttt{f :: Rec -> T},
we define \texttt{f\_\_ :: (T -> T) -> Rec -> Rec}
and derive \texttt{f\_ :: T -> Rec -> Rec}.
\begin{code}
data REqState
 = ReqState {
      known :: [VarTable]
    , laws :: [Term]
    , goal :: Term
    }
known__ f r = r{known = f $ known r} ; known_  = known__ . const
laws__  f r = r{laws  = f $ laws r}  ; laws_   = laws__  . const
goal__  f r = r{goal  = f $ goal r}  ; goal_   = goal__  . const
\end{code}

\begin{code}
initState :: [String] -> IO REqState
initState args = return $
  ReqState
    []                           -- known :: [VarTable]
    []                           -- laws :: [Term]
    (Val P $ Txt $ concat args)  -- goal :: Term

summariseREqS reqs = show $ goal reqs
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
 , "Type '?' for help."
 ]

loop :: REqState -> InputT IO ()
loop reqs = do
   minput <- getInputLine (summariseREqS reqs++' ':_equiv++" ")
   case minput of
       Nothing      ->  quit reqs
       Just "quit"  ->  quit reqs
       Just input   ->  docommand reqs (words input) >>= loop

-- may ask for user confirmation, amd save? stuff..
quit reqs = outputStrLn "Goodbye!"
\end{code}

REPL command repository types and lookup:
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
\end{code}

Command dispatch:
\begin{code}
docommand reqs [] = return reqs
docommand reqs ("?":what)
 = help reqs what
docommand reqs (cmd:args)
 = case clookup cmd commands of
     Nothing -> outputStrLn ("unknown cmd: '"++cmd++"', '?' for help.") >> return reqs
     Just (_,_,_,c)  ->  c args reqs
\end{code}

Command Help
\begin{code}
help reqs []
  = do outputStrLn "Commands:"
       outputStrLn "'?'     -- this help message"
       outputStrLn "'? cmd' -- help for 'cmd'"
       outputStrLn "Control-D or 'quit'  -- exit program."
       outputStrLn $ unlines $ map shorthelp commands
       return reqs
  where shorthelp (cmd,sh,_,_) = cmd ++ "  -- " ++ sh

help reqs (what:_)
  = case clookup what commands of
     Nothing -> outputStrLn ("unknown cmd: '"++what++"'") >> return reqs
     Just (_,_,lh,_) -> outputStrLn lh >> return reqs
\end{code}

\newpage
The command repository:
\begin{code}
commands :: Commands
commands = [cmdX]

cmdX
  = ( "X"
    , "'x'"
    , "the mysterious 'X' !"
    , xcomm )
  where
     xcomm _ reqs = do outputStrLn "X! Whoo! X!"
                       return (goal__ addX reqs)
     addX (Val P (Txt s)) = Val P $ Txt ('X':s)
     addX t = t
\end{code}
