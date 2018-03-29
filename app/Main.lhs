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
import Data.Set (Set)
import qualified Data.Set as S
import Data.List
import Data.Maybe

import NiceSymbols hiding (help)

import Utilities
import LexBase
import Variables
import AST
import VarData
import SideCond
import TermZipper
import Proof
import Propositions
import TestRendering
\end{code}

\begin{code}
name = "reasonEq"
version = "0.5.0.0++"
\end{code}

\begin{code}
main :: IO ()
main
  = do args <- getArgs
       if "-g" `elem` args
       then do putStrLn "starting GUI..."
               gui (args \\ ["-g"])
       else do putStrLn "starting REPL..."
               repl args
\end{code}

\newpage
\subsection{System State}

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
    , laws :: [(String,Assertion)]
    , conj :: [(String,Assertion)]
    , goal :: Maybe (String,Assertion)
    , proof :: Maybe LiveProof
    }
known__ f r = r{known = f $ known r} ; known_  = known__ . const
laws__  f r = r{laws  = f $ laws r}  ; laws_   = laws__  . const
conj__  f r = r{conj  = f $ conj r}  ; conj_   = conj__  . const
goal__  f r = r{goal  = f $ goal r}  ; goal_   = goal__  . const
proof__ f r = r{proof = f $ proof r} ; proof_  = proof__ . const
\end{code}

\begin{code}
initState :: [String] -> IO REqState
initState []
  = do putStrLn "Running in normal user mode."
       return $ ReqState [] [] [] Nothing Nothing
initState ["dev"]
  = do putStrLn "Running in development mode."
       let reqs = ReqState [propKnown] propLaws propConjs Nothing Nothing
       return reqs

summariseREqS :: REqState -> String
summariseREqS reqs
 = intcalNN ":" [ show $ length $ known reqs
                , show $ length $ laws reqs
                , show $ length $ conj reqs
                , case goal reqs of
                   Nothing -> ""
                   _ -> "!"
                , case proof reqs of
                   Nothing -> ""
                   _ -> "!"
                ]
\end{code}

\subsubsection{The Show Command}
Showing known variables:
\begin{code}
showKnown vts = unlines $ map trVarTable $ vts
\end{code}

Showing laws:
\begin{code}
showLaws lws = unlines $ map (showLaw (nameWidth lws)) $ lws

nameWidth lws = maximum $ map (length . getName) lws
getName (n,_) = n

showLaw w (n,(t,sc))
  = ldq ++ n ++ rdq ++ pad w n ++ "  " ++ trTerm 0 t ++ "  "++trSideCond sc

pad w n
  | ext > 0    =  replicate ext ' '
  | otherwise  =  ""
  where ext = w - length n
\end{code}

Showing Goal:
\begin{code}
showGoal Nothing = "no Gooal."
showGoal (Just goal) = showLaw 0 goal
\end{code}

Showing Proof:
\begin{code}
showProof Nothing = "no Proof."
showProof (Just proof) = "Can't show Proofs yet."
\end{code}

\subsubsection{Set Command}

Set Goal:


\newpage
\subsection{GUI Top-Level}
\begin{code}
gui :: [String] -> IO ()
gui args = putStrLn $ unlines
         [ "Welcome to "++name++" "++version
         , "GUI N.Y.I.!"
         , "Goodbye" ]
\end{code}

\newpage
\subsection{REPL Top-Level}
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
     Nothing -> outputStrLn ("unknown cmd: '"++cmd++"', '?' for help.")
                 >> return reqs
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
\subsection{Command Repository}
\begin{code}
commands :: Commands
commands = [cmdShow,cmdSet]
\end{code}

\subsubsection{Show Command }
\begin{code}
cmdShow :: CommDescr
cmdShow
  = ( "sh"
    , "show parts of the prover state"
    , unlines
        [ "sh "++shKnown++" - show known variables"
        , "sh "++shLaws++" - show current laws"
        , "sh "++shConj++" - show current conjectures"
        , "sh "++shGoal++" - show current goal"
        , "sh "++shProof++" - show current proof"
        ]
    , showState )

shKnown = "k"
shLaws  = "l"
shConj = "c"
shGoal = "g"
shProof = "p"

showState [cmd] reqs
 | cmd == shKnown  =  doshow reqs $ showKnown $ known reqs
 | cmd == shLaws   =  doshow reqs $ showLaws  $ laws  reqs
 | cmd == shConj   =  doshow reqs $ showLaws  $ conj  reqs
 | cmd == shGoal   =  doshow reqs $ showGoal  $ goal  reqs
 | cmd == shProof  =  doshow reqs $ showProof $ proof reqs
showState _ reqs   =  doshow reqs "unknown 'show' option."

doshow reqs str
 = do outputStrLn str
      return reqs
\end{code}

\subsubsection{Set Command}
\begin{code}
cmdSet
  = ( "set"
    , "set parts of prover state"
    , unlines
       [ "set goal name - set goal to named conjecture"]
    , setState )

setState [what,name] reqs
 | what == "goal"  =  setgoal reqs name
setState _ reqs = doshow reqs "unknown 'set' option"

setgoal reqs name
  = case alookup name $ conj reqs of
      Nothing -> doshow reqs ("conjecture '"++name++"' not found.")
      Just cnj -> return $ goal_ (Just cnj) reqs

-- association list lookup
alookup name [] = Nothing
alookup name (thing@(n,_):rest)
  | name == n  =  Just thing
  | otherwise  =  alookup name rest
\end{code}

\subsubsection{Prove Command}
\begin{code}
cmdProve
  = ( "prove"
    , "do a proof"
    , [ "prove - prove current goal"]
    , "tbd" )
\end{code}
