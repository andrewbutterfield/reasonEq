\section{Generic REPL Code}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module REPL (
    REPLParser, REPLArguments, idParse, wordParse, charTypeParse
  )
where

-- import System.Environment
import System.Console.Haskeline
import Control.Monad.IO.Class
-- import Data.Map (Map)
-- import qualified Data.Map as M
-- import Data.Set (Set)
-- import qualified Data.Set as S
-- import Data.List
-- import Data.Maybe
import Data.Char
\end{code}

\subsection{REPL Introduction}

A ``REPL''%
\footnote{
Read-Execute-Print-Loop,
}%
 involves getting user-input,
and then using that to produce some form of state transformation
with user feedback.
Here we provide a pre-packaged REPL, parameterised by:
\begin{itemize}
  \item Welcome (\texttt{wlcm})
  \item user prompt and parsing (\texttt{pp})
  \item command descriptors (\texttt{cds})
  \item state (\texttt{state})
\end{itemize}

We consider a REPL as always having two special-purpose commands,
one to exit the REPL, another to provide help,
while the rest are viewed as I/O actions that also modify state.

A parser converts strings to lists of strings.
The key point here is that the first string, if present,
determines what command will be run,
with the remaining strings passed as arguments to that command
We define some simple obvious parsers as well.
\begin{code}
type REPLParser = String -> [String]
type REPLArguments = [String]

idParse, wordParse, charTypeParse :: REPLParser
idParse s = [s] -- return user string completely unaltered
wordParse = words -- break into max-length runs without whitespace
charTypeParse -- group letter,digits, and other non-print
 = concat . map (segment []) . words
 where
   segment segs "" = reverse segs
   segment segs (c:cs)
    | isAlpha c = segment' isAlpha segs [c] cs
    | isDigit c = segment' isDigit segs [c] cs
    | c == '-'  = segment' isDigit segs [c] cs
    | otherwise = segment' notAlphNum segs [c] cs
   segment' p segs [] ""  = reverse segs
   segment' p segs seg ""  = reverse (reverse seg:segs)
   segment' p segs seg str@(c:cs)
    | p c = segment' p segs (c:seg) cs
    | otherwise  = segment (reverse seg:segs) str
   notAlphNum c
    | isAlpha c  =  False
    | isDigit c  =  False
    | otherwise  =  True
\end{code}

\begin{code}
type REPLCmd state = REPLArguments -> state -> InputT IO state
type REPLCmdDescr state
  = ( String     -- command name
    , String     -- short help for this command
    , String     -- long help for this command
    , REPLCmd state)  -- command function
type REPLExit state = REPLArguments -> state -> InputT IO (Bool,state)
type REPLCommands state
  = ( [String], REPLExit state -- all quit commands, quit command
    , [String] -- all help commands
    , [REPLCmdDescr state]
    )
\end{code}


\subsubsection{Command Respository Lookup}
\begin{code}
cmdLookup :: String -> [REPLCmdDescr state] -> Maybe (REPLCmdDescr state)
cmdLookup s []= Nothing
cmdLookup s (cd@(n,_,_,_):rest)
 | s == n     =  Just cd
 | otherwise  =  cmdLookup s rest
\end{code}


We have a configuration that defines the REPL behaviour
that does not change during its lifetime:
\begin{code}
data REPLConfig state
  = REPLC {
      replPrompt :: state -> String
    , replInterrupt :: [String]
    , replParser :: REPLParser
    }

defConfig
  = REPLC
      (const "repl: ")
      ["interrupted !"]
      charTypeParse
\end{code}

\begin{code}
runREPL :: String
        -- -> (state -> String) -> parser -> cds -> exit
        -> REPLConfig state
        -> state -> IO ()
runREPL wlcm config s0
  = runInputT defaultSettings (welcome wlcm >> loopREPL config s0)

welcome :: String -> InputT IO ()
welcome wlcm = outputStrLn wlcm
\end{code}

Loop simply gets users input and dispatches on it
\begin{code}
loopREPL :: REPLConfig state -> state -> InputT IO ()
loopREPL config s
  = do inp <- inputREPL config s
       outputStrLn $ show inp
       -- dispatchREPL pp cds exit s inp
\end{code}

Input generates a prompt that may or may not depend on the state,
and then checks and transforms
\begin{code}
inputREPL :: REPLConfig state -> state -> InputT IO [String]
inputREPL config s
  = do minput <- getInputLine (replPrompt config s)
       case minput of
         Nothing     ->  return $ replInterrupt config
         Just input  ->  return $ replParser config input
\end{code}
%
% Dispatch checks input to see if it requires exiting,
% in which case it invokes the exit protocol (which might not exit!)
% Otherwise it executed the designated command.
% \begin{code}
% data Cmd cd inp = QUIT | HELP | CMD cd inp
% dispatchREPL :: (state -> (String,parse,nullhandler)) -> cds -> exit -> state -> inp -> InputT IO ()
% dispatchREPL pp cds exit s inp
%   = case lookupREPL cds inp of
%       QUIT -> exitREPL pp cds exit s
%       HELP -> helpREPL pp cds exit s
%       CMD cd inp' -> doCMD pp cds exit s cd inp'
% \end{code}
%
% \begin{code}
% exitREPL pp cds exit s = return ()
% helpREPL pp cds exit s
%   = do help cds
%        loopREPL pp cds exit s
%   where help = outputStrLn "help nyi"
% doCMD pp cds exit s cd inp
%   = do outputStrLn "doCMD NYI"
%        loopREPL pp cds exit s
% \end{code}
%
%
% \subsubsection{Command Repository}
% \begin{code}
% reqREPLcommands :: Commands s
% reqREPLcommands = []
% \end{code}
%
% \subsubsection{Command Dispatch}
% \begin{code}
% docommand :: s -> [String] -> InputT IO s
% docommand reqs [] = return reqs
% docommand reqs ("?":what)
%  = help reqs what
% docommand reqs (cmd:args)
%  = case clookup cmd reqREPLcommands of
%      Nothing -> outputStrLn ("unknown cmd: '"++cmd++"', '?' for help.")
%                  >> return reqs
%      Just (_,_,_,c)  ->  c args reqs
% \end{code}
%
% \subsubsection{Command Help}
% \begin{code}
% help reqs []
%   = do outputStrLn "Commands:"
%        outputStrLn "'?'     -- this help message"
%        outputStrLn "'? cmd' -- help for 'cmd'"
%        outputStrLn "Control-D or 'quit'  -- exit program."
%        outputStrLn $ unlines $ map shorthelp reqREPLcommands
%        return reqs
%   where shorthelp (cmd,sh,_,_) = cmd ++ "  -- " ++ sh
%
% help reqs (what:_)
%   = case clookup what reqREPLcommands of
%      Nothing -> outputStrLn ("unknown cmd: '"++what++"'") >> return reqs
%      Just (_,_,lh,_) -> outputStrLn lh >> return reqs
% \end{code}
