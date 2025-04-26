\chapter{Generic REPL Code}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.REPL (
    REPLParser, REPLArguments, idParse, wordParse, charTypeParse
  , REPLCmd, REPLCmdDescr, REPLExit, REPLCommands
  , REPLConfig(..)
  , runREPL
  , userPrompt, userPause
  , clearIt, clear
  , waitForReturn
  , NewStatus(..)
  , showAndQuery
  , clearLong
  , putListOneLine
  , pickByNumber
  , selectPairings, pickPairing
  , pickThing, pickOrProvideThing, pickThings, takeThings
  , getConfirmedObject
  )
where

import System.Console.Haskeline
import System.IO
import Control.Monad.IO.Class
import Data.List
import Data.Char

import YesBut
import Utilities
\end{code}

\section{REPL Introduction}

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

\newpage
A parser converts strings to lists of strings.
The key point here is that the first string, if present,
determines what command will be run,
with the remaining strings passed as arguments to that command.
We define some simple obvious parsers as well.
\begin{code}
type REPLArguments = [String]
type REPLParser = String -> REPLArguments

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
type REPLCmd state = REPLArguments -> state -> IO state
type REPLCmdDescr state
  = ( String     -- command name
    , String     -- short help for this command
    , String     -- long help for this command
    , REPLCmd state)  -- command function
type REPLExit state = REPLArguments -> state -> IO (Bool,state)
type REPLCommands state = [REPLCmdDescr state]
\end{code}

We have a configuration that defines the REPL behaviour
that does not change during its lifetime:
\begin{code}
data REPLConfig state
  = REPLC {
      replPrompt :: Bool -> state -> String
            -- justHelped :: Bool, true if help messages have just been printed
    , replEOFReplacement :: [String]
    , replParser :: REPLParser
    , replQuitCmds :: [String]
    , replQuit :: REPLExit state
    , replHelpCmds :: [String]
    , replCommands :: REPLCommands state
    , replEndCondition :: state -> Bool
    , replEndTidy :: REPLCmd state
    }
\end{code}

\newpage
A default REPL configuration for test purposes
\begin{code}
defConfig
  = REPLC
      (const $ const "repl: ")
      ["ignoring EOF"]
      charTypeParse
      ["quit","x"]
      defQuit
      ["help","?"]
      tstCmds
      defEndCond
      defEndTidy

defQuit _ s
  = do putStrLn "\nGoodbye!\n"
       return (True,s)

tstCmds
  = [ ("test"
      , "simple test"
      , "raises all arguments to uppercase"
      , tstCmd
      )
    ]

tstCmd args s
  = do putStrLn (show $ map (map toUpper) args)
       putStrLn "Test complete"
       return s

defEndCond _ = False
defEndTidy _ s = return s
\end{code}

\newpage
\subsection{Command Respository Lookup}
\begin{code}
cmdLookup :: String -> REPLCommands state -> Maybe (REPLCmdDescr state)
cmdLookup s []= Nothing
cmdLookup s (cd@(n,_,_,_):rest)
 | s == n     =  Just cd
 | otherwise  =  cmdLookup s rest
\end{code}


\begin{code}
runREPL :: String
        -> REPLConfig state
        -> state -> IO state
runREPL wlcm config s0
  = runInputT defaultSettings (welcome wlcm >> loopREPL config True s0)

welcome :: String -> InputT IO ()
welcome wlcm = outputStrLn wlcm
\end{code}

Loop simply gets users input and dispatches on it
\begin{code}
loopREPL :: REPLConfig state -> Bool -> state -> InputT IO state
loopREPL config justHelped s
  = if replEndCondition config s
     then liftIO $ replEndTidy config [] s
     else do inp <- inputREPL config justHelped s
             dispatchREPL config justHelped s inp
\end{code}

Input generates a prompt that may or may not depend on the state,
and then checks and transforms
\begin{code}
inputREPL :: REPLConfig state -> Bool -> state -> InputT IO [String]
inputREPL config justHelped s
  = do minput <- getInputLine (replPrompt config justHelped s)
       case minput of
         Nothing     ->  return $ replEOFReplacement config
         Just input  ->  return $ replParser config input
\end{code}

Dispatch first checks input to see if it requires exiting,
in which case it invokes the exit protocol (which might not exit!).
Then it sees if the help command has been given,
and enacts that.
Otherwise it executes the designated command.
\begin{code}
dispatchREPL :: REPLConfig state -> Bool -> state -> [String] -> InputT IO state
dispatchREPL config justHelped s []
  = loopREPL config justHelped s
dispatchREPL config justHelped s (cmd:args)
  | cmd `elem` replQuitCmds config
    = do (go,s') <- liftIO $ replQuit config args s
         if go then return s'
               else loopREPL config False s'
  | cmd `elem` replHelpCmds config
    = do helpREPL config s args
         loopREPL config True s
  | otherwise
    = case cmdLookup cmd (replCommands config) of
        Nothing
          -> do outputStrLn ("No such command '"++cmd++"'")
                loopREPL config justHelped s
        Just (_,_,_,cmdFn)
          -> do s' <- liftIO $ cmdFn args s
                loopREPL config False s'
\end{code}

Help with no arguments shows the short help for all commands.
Help with an argument that corresponds to a command shows the
long help for that command.
\begin{code}
helpREPL :: REPLConfig state -> state -> [String] -> InputT IO ()
helpREPL config s []
  = do outputStrLn ""
       outputStrLn ((intercalate "," $ replQuitCmds config)++" -- exit")
       outputStrLn ((intercalate "," $ replHelpCmds config)++" -- this help text")
       outputStrLn ((intercalate "," $ replHelpCmds config)++" <cmd> -- help for <cmd>")
       shortHELP $ replCommands config
       outputStrLn ""
helpREPL config s (cmd:_)
 | cmd `elem` replQuitCmds config = outputStrLn (cmd ++ " -- exits program")
 | cmd `elem` replHelpCmds config = outputStrLn (cmd ++ " -- provides help")
 | otherwise  =  longHELP cmd (replCommands config)
\end{code}

\begin{code}
shortHELP :: REPLCommands state -> InputT IO ()
shortHELP [] = return ()
shortHELP ((nm,shelp,_,_):cmds)
  = do outputStrLn ( nm ++ " -- " ++ shelp )
       shortHELP cmds
\end{code}

\begin{code}
longHELP :: String -> REPLCommands state -> InputT IO ()
longHELP cmd []  = outputStrLn ("No such command: '"++cmd++"'")
longHELP cmd ((nm,_,lhelp,_):cmds)
  | cmd == nm  = outputStrLn ("\n"++lhelp++"\n")
  | otherwise  =  longHELP cmd cmds
\end{code}

\newpage
\section{REPL Utilities}

\subsection{Useful IO bits and pieces}

Prompting:
\begin{code}
userPrompt :: String -> IO String
userPrompt str = putStr str >> hFlush stdout >> getLine
\end{code}

Screen clearing:
\begin{code}
clear = "\ESC[2J\ESC[1;1H"
clearIt str = clear ++ str
\end{code}

Pausing (before \textrm{clearIt}, usually)
\begin{code}
userPause = userPrompt "hit <enter> to continue"
\end{code}


\subsection{Response Waiting}

We sometimes want to wait:
\begin{code}
waitForReturn :: IO ()
waitForReturn
  = do putStrLn "<return> to continue"
       getLine
       return ()
\end{code}
Sometime we show what was entered and offer to keep, re-enter, or exit:
\begin{code}
data NewStatus = Reject | ReDo | Keep
showAndQuery :: String -> IO NewStatus
showAndQuery str
  = do putStrLn "Specified:\n"
       putStrLn str
       putStrLn "Keep/eXit  k/x ?  (anything else means re-enter)"
       response <- getLine
       case take 1 response of
         ['k']  ->  return Keep
         ['x']  ->  return Reject
         _      ->  return ReDo
\end{code}



\subsection{Screen Clearing}

Screen clearing for help strings:
\begin{code}
clearLong :: REPLCmdDescr s -> REPLCmdDescr s
clearLong (nm,short,long,func) = (nm,short,clearIt long,func)
\end{code}

\subsection{Dislaying List as One-liner}

\begin{code}
putListOneLine showx [] = putStrLn ""
putListOneLine showx [x] = putStrLn (showx x)
putListOneLine showx (x:xs)
  = putStr (showx x ++ " ") >> putListOneLine showx xs
\end{code}

\subsection{List Picking by Number}

\begin{code}
pickByNumber :: String -> (t -> String) -> t -> IO Int
pickByNumber prompt showx x
  = do putStrLn $ showx x
       putStr prompt ; hFlush stdout ; input <- getLine
       return $ readNat $ trim input

\end{code}

\newpage

\subsection{Pair Picking by Number}

Basic picker, assuming context already displayed.
\begin{code}
selectPairings :: (a -> String)  -- prompt generator
               -> [(a,b)]        -- accumulated pairs so far
               -> [b]            -- things being picked to go with ...
               -> [a]            -- ... these things
               -> IO ( Bool      -- true if user cancels
                     , [(a,b)] ) -- result pairing
selectPairings prompt pairs _ []  = return (False,pairs)
selectPairings prompt pairs bs as@(a:as')
  = do putStr (prompt a ++ " (0 to cancel) ? ")
       hFlush stdout; input <- getLine
       case input of
         str@(_:_) | all isDigit str
           -> let i = read str in
              if i == 0 then return (True,pairs)
              else case nlookup (read str) $ bs of
               Just b
                 -> selectPairings prompt ((a,b):pairs) bs as'
               _ -> selectPairings prompt pairs bs as
         _ -> selectPairings prompt pairs bs as
\end{code}

Full picker, that generates context display.
This is when the context is helpful information for the user when picking.
\begin{code}
pickPairing :: String                  -- describe context
            -> (c -> String)           -- display context
            -> String -> (a -> String)
            -> String -> (b -> String)
            -> (a -> String)
            -> c                       -- context
            -> [a] -> [b]
            -> IO (Bool,[(a,b)])
pickPairing
  whatCtxt showCtxt
  whatA showA
  whatB showB
  prompt
  ctxt as bs
  = do putStrLn (whatCtxt++showCtxt ctxt)
       putStr whatA
       putListOneLine showA as
       putStrLn whatB
       putStrLn $ numberList showB bs
       selectPairings prompt [] bs as
\end{code}


\section{Better(?) Pickers}

\begin{code}
inRange :: Int -> Int -> Bool
inRange size choice = choice >= 1 && choice <= size

selectFrom things choice = things!!(choice-1)

pickError msg = return (False,error msg)
\end{code}

\newpage

Pick one thing from a list.
\begin{code}
pickThing :: String -> (a -> String) -> [a] -> IO (Bool,a)
pickThing hdr showThing [] = pickError "Nothing to choose"
pickThing hdr showThing [thing] = return (True,thing)
pickThing hdr showThing things
  = do putStrLn hdr
       putStrLn $ numberList showThing things
       choice <- fmap readNat $ userPrompt "Select by number: "
       if inRange (length things) choice
         then do let thing = selectFrom things choice
                 putStrLn ("Chosen "++showThing thing)
                 return (True,thing)
         else pickError "Bad choice!"
\end{code}

Pick one thing from a list, or accept a user-supplied string
\begin{code}
pickOrProvideThing :: String -> (a -> String) -> (String -> a) -> [a] 
                   -> IO (Bool,a)
pickOrProvideThing hdr showThing str2Thing things
  = do putStrLn hdr
       putStrLn $ numberList showThing things
       response <- userPrompt "Select by number or provide string: "
       let choice = readNat response
       if choice == (-1)
       then do putStrLn ("Chosen "++response)
               return(True,str2Thing response)
       else
        if inRange (length things) choice
          then do let thing = selectFrom things choice
                  putStrLn ("Chosen "++showThing thing)
                  return (True,thing)
          else pickError "Bad choice!"
\end{code}

Pick zero or more things from a list.
\begin{code}
pickThings :: String -> (a -> String) -> [a] -> IO (Bool,[a])
pickThings hdr showThing [] = pickError "No things to be chosen"
pickThings hdr showThing things
  = do putStrLn hdr
       putStrLn $ numberList showThing things
       choicesTxt <- userPrompt "Select by numbers: "
       let choices =  map readNat $ words choicesTxt
       putStrLn ("Choices = "++show choices)
       if null choices
         then return (False,error "Nothing chosen!")
       else if all (inRange size) choices
         then do let wanted = map (selectFrom things) choices
                 putStrLn ("Chosen "++unwords (map showThing wanted))
                 return (True,wanted)
         else return (False,error "Bad choices!")
  where size = length things
\end{code}

Take things (pick and remove) from a list, returning takings and leftovers.
\begin{code}
takeThings :: String -> (a -> String) -> [a] -> IO (Bool,([a],[a]))
takeThings hdr showThing [] = pickError "No things to be taken"
takeThings hdr showThing things
  = do putStrLn hdr
       putStrLn $ numberList showThing things
       choicesTxt <- userPrompt "Select by numbers: "
       let choices =  map readNat $ words choicesTxt
       putStrLn ("Choices = "++show choices)
       if null choices
         then return (True,([],things)) -- can choose nothing!
       else if all (inRange size) choices && choices == nub choices
         then do let (wanted,leftover) = takeOut choices things
                 putStrLn ("Taken "++unwords (map showThing wanted))
                 putStrLn ("Remaining "++unwords (map showThing leftover))
                 return (True,(wanted,leftover))
         else return (False,error "Bad takings!")
  where
    size = length things
    takeOut choices things
      = ( map (selectFrom things) choices
        , removeChoices 1 (sort choices) things)
    removeChoices _ [] things = things
    removeChoices _ _  []     = []
    removeChoices i choices@(choice:crest) things@(thing:trest)
      | i >  choice  =  removeChoices (i+1) crest things
      | i == choice  =  removeChoices (i+1) crest trest
      | otherwise    =  thing : removeChoices (i+1) choices trest
\end{code}

Parse user input, display outcome, and request user confirmation.
\begin{code}
getConfirmedObject :: String -> (String -> YesBut b) -> (b -> String)
                   -> IO (Bool, b)
getConfirmedObject prompt parse preview =
  do  objTxt <- userPrompt prompt
      case parse objTxt of
        But msgs  ->  objParseFailed prompt parse preview msgs
        Yes obj ->
          do  response <- showAndQuery $ preview obj
              case response of
                Reject  ->  return (False,obj)
                Keep    ->  return (True,obj)
                ReDo    ->  getConfirmedObject prompt parse preview

objParseFailed prompt parse preview msgs =
  do putStrLn $ unlines' msgs
     response <- userPrompt "retry? [Y/n] (default Y)"
     case take 1 response of
       "n"  ->  return (False,undefined)
       _    ->  getConfirmedObject prompt parse preview       
\end{code}