\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.Environment
import System.IO
import System.FilePath
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char

import NiceSymbols hiding (help)

import Utilities
import StratifiedDAG
import Persistence

import LexBase
import Variables
import AST
import VarData
import SideCond
import Binding
import REqState
import AbstractUI
import PropAxioms
import Instantiate
import TestRendering
import REPL
import Dev
\end{code}

\begin{code}
name = "reasonEq"
version = "0.6.9.0"
\end{code}

\newpage
\subsection{\texttt{main}}

The program takes command-line arguments
that tailor its behaviour.
For now, we consider the following behavioural aspects:
\begin{description}
  \item [UI]
    we propose to support both a text-based REPL
    and a graphical user-interface. The REPL is the default,
    while the GUI can be invoked with the \texttt{-g} argument (anywhere).
  \item [FS]
    we allow the specification of where in the filesystem the prover data files
    are kept.
    We support a project-based approach, where a project is simply
    a folder (``workspace'') containing all relevant files.
    We can specify the path to same using the \texttt{-p} command-line option.
    We also have the notion of a single seperate folder with global data
    that gives the locations of all known project folders,
    plus any other global configuration data.
    This can be specified with the \texttt{-c} flag.
    We also provide a mechanism for locating these if no specific command-line
    arguments are supplied.
    We will also support getting such filepath and config information
    from a \texttt{.req} folder if present at the current working directory
    from which the program was invoked.
    In particular we use a design that allows the program itself
    to setup global configuration data, in an OS-dependent manner.
  \item [Dev]
    we also allow two modes when running: ``User'' and ``Dev''.
    In User mode all prover state is loaded from data files,
    as specified by FS above.
    In Dev mode, some prover state may be pre-installed.
    Dev mode is the default at present,
    while User mode is invoked by the first argument being \texttt{-u}.
\end{description}

So we can summarise flags as follows:
\begin{code}
configFlag  = "-c"    -- <path>   path to prover configuration files
guiFlag     = "-g"    --          use GUI instead of REPL
projectFlag = "-p"    -- <path>   path to prover data files
userFlag    = "-u"    --          run in 'User' mode
cwdConfig   = ".req"  -- local config folder
\end{code}

We shall define a record to record flag data,
and a corresponding parser:
\begin{code}
data CMDFlags = CMDFlags { config  :: Maybe FilePath
                         , usegui  :: Bool
                         , project :: Maybe FilePath
                         , user    :: Bool}

defFlags = CMDFlags { config  = Nothing
                    , usegui  = False
                    , project = Nothing
                    , user    = False }

parseArgs args = parse defFlags args where
  parse flags [] = flags
  parse flags (f:p:ss)
   | f == configFlag   =  parse flags{ config  = checkfp p } ss
   | f == projectFlag  =  parse flags{ project = checkfp p } ss
   where checkfp fp
           | isValid fp  =  Just fp
           | otherwise   =  Nothing
  parse flags (f:ss)
   | f == guiFlag      =  parse flags{ usegui  = True }   ss
   | f == userFlag     =  parse flags{ user    = True }   ss
   -- ignore anything else
   | otherwise         =  parse flags                     ss
\end{code}

\begin{code}
main :: IO ()
main
  = do args <- getArgs
       let flags = parseArgs args
       if usegui flags
       then do putStrLn "starting GUI..."
               gui flags
       else do putStrLn "starting REPL..."
               repl flags
\end{code}


\newpage
\subsection{Initialising State}

At present, we assume development mode by default.

The normal ``user'' mode is still not of much use,
but there will soon be a way to test it.
\begin{code}
initState :: CMDFlags -> IO REqState

initState flags
  = if user flags
    then case project flags of
           Nothing -> do putStrLn "Running user mode, default initial state."
                         return reqstate0
           Just fp -> do putStrLn "Running user mode, loading project state."
                         readState fp
    else do putStrLn "Running in development mode."
            case project flags of
              Nothing -> return $ devInitState
              -- we don't load from fp in dev. mode
              -- a 'load' as first command will do that
              Just fp -> return $ devInitState{ projectDir = fp }

reqstate0 = REqState { projectDir = ""
                     , logicsig = propSignature
                     , theories = noTheories
                     , currTheory = ""
                     , liveProofs = M.empty }
\end{code}

\newpage
\subsection{GUI Top-Level}
\begin{code}
gui :: CMDFlags -> IO ()
gui flags = putStrLn $ unlines
         [ "Welcome to "++name++" "++version
         , "GUI N.Y.I.!"
         , "Goodbye" ]
\end{code}

\newpage
\subsection{REPL Top-Level}

We define our reasonEq REPL types first:
\begin{code}
type REqCmd       =  REPLCmd      REqState
type REqCmdDescr  =  REPLCmdDescr REqState
type REqExit      =  REPLExit     REqState
type REqCommands  =  REPLCommands REqState
type REqConfig    =  REPLConfig   REqState
\end{code}

Now we work down through the configuration components.
\begin{code}
reqPrompt :: Bool -> REqState -> String
reqPrompt _ _ = _equiv++" : "

reqEOFreplacmement = [nquit]

reqParser = charTypeParse

reqQuitCmds = [nquit] ; nquit = "quit"

reqQuit :: REqExit
-- may ask for user confirmation, and save? stuff..
reqQuit _ reqs = putStrLn "\nGoodbye!\n" >> return (True, reqs)
-- need to save persistent state on exit

reqHelpCmds = ["?","help"]

reqCommands :: REqCommands
reqCommands = [ cmdShow, cmdSet
              , cmdNewProof, cmdRet2Proof
              , cmdSave, cmdLoad
              , cmdBuiltin ]

-- we don't use these features in the top-level REPL
reqEndCondition _ = False
reqEndTidy _ reqs = return reqs
\end{code}

The configuration:
\begin{code}
reqConfig
  = REPLC
      reqPrompt
      reqEOFreplacmement
      reqParser
      reqQuitCmds
      reqQuit
      reqHelpCmds
      reqCommands
      reqEndCondition
      reqEndTidy
\end{code}

\begin{code}
repl :: CMDFlags -> IO ()
repl flags
  = do reqs0 <- initState flags
       runREPL reqWelcome reqConfig reqs0
       return ()

reqWelcome = unlines
 [ "Welcome to the "++name++" "++version++" REPL"
 , "Type '?' for help."
 ]
\end{code}


\newpage
\subsection{Show Command }
\begin{code}
cmdShow :: REqCmdDescr
cmdShow
  = ( "sh"
    , "show parts of the prover state"
    , unlines
        [ "sh "++shProject++" -- show current project"
        , "sh "++shSig++" -- show logic signature"
        , "sh "++shTheories++" -- show theories"
        , "sh "++shLaws++" -- show laws"
        , "sh "++shCurrThry++" -- show 'current' theory"
        , "sh "++shConj++" -- show current conjectures"
        , "sh "++shLivePrf++" -- show current (live) proof"
        , "sh "++shProofs++" -- show completed proofs"
        ]
    , showState )

shProject = "f"
shSig = "s"
shTheories = "t"
shLaws = "L"
shCurrThry = "T"
shConj = "c"
shLivePrf = "p"
shProofs = "P"

-- these are not robust enough - need to check if component is present.
showState [cmd] reqs
 | cmd == shProject   =  doshow reqs $ projectDir reqs
 | cmd == shSig       =  doshow reqs $ observeSig reqs
 | cmd == shTheories  =  doshow reqs $ observeTheories reqs
 | cmd == shLaws      =  doshow reqs $ observeLaws reqs
 | cmd == shCurrThry  =  doshow reqs $ observeCurrTheory reqs
 | cmd == shConj      =  doshow reqs $ observeCurrConj reqs
 | cmd == shLivePrf   =  doshow reqs $ observeLiveProofs reqs
 | cmd == shProofs    =  doshow reqs $ observeCompleteProofs reqs
showState _ reqs      =  doshow reqs "unknown 'show' option."

doshow reqs str  =  putStrLn str >> return reqs
\end{code}

\newpage
\subsection{State Save and Restore}


\begin{code}
cmdSave, cmdLoad :: REqCmdDescr
cmdSave
  = ( "save"
    , "save prover state to file"
    , unlines
        [ "save -- save all prover state to current project"
        , "save <thry> -- save theory <thry> to current project"]
    , saveState )
cmdLoad
  = ( "load"
    , "load prover state from file"
    , unlines
        [ "load -- load prover state from current project"
        , "load <thry> -- load EXISTING theory <thry> from current project"]
    , loadState )

saveState [] reqs
  = do writeState reqs
       putStrLn ("REQ-STATE written to '"++projectDir reqs++"'.")
       return reqs
saveState [nm] reqs
  = case getTheory nm $ theories reqs of
      Nothing
       -> do putStrLn ("No such theory: '"++nm++"'")
             return reqs
      Just thry
       -> do writeNamedTheory reqs (nm,writeTheory thry)
             putStrLn ("Theory '"++nm++"' written to '"++projectDir reqs++"'.")
             return reqs
saveState _ reqs  =  doshow reqs "unknown 'save' option."

loadState [] reqs
  = do let dirfp = projectDir reqs
       reqs' <- readState dirfp
       putStrLn ("REQ-STATE read from '"++dirfp++"'.")
       return reqs'
loadState [nm] reqs
  = do let dirfp = projectDir reqs
       (nm,thry) <- readNamedTheory dirfp nm
       putStrLn ("Theory '"++nm++"'read from  '"++projectDir reqs++"'.")
       return $ theories__ (replaceTheory thry) reqs
loadState _ reqs  =  doshow reqs "unknown 'load' option."
\end{code}

\newpage
\subsection{Set Command}
\begin{code}
cmdSet :: REqCmdDescr
cmdSet
  = ( "set"
    , "set parts of the prover state"
    , unlines
        [ "set "++setCurrThry++" 'name' -- set current theory to 'name'"]
    , setState )

setCurrThry = shCurrThry

setState (cmd:rest) reqs
 | cmd == setCurrThry
    =  case setCurrentTheory thnm reqs of
         Nothing     ->  doshow reqs  ("No such theory: '"    ++ thnm ++ "'")
         Just reqs'  ->  doshow reqs' ("Current Theory now '" ++ thnm ++ "'")
 where thnm = args2str rest
setState _ reqs      =  doshow reqs "unknown 'set' option."
\end{code}


\newpage
\subsection{Proving Commands}

\begin{code}
cmdNewProof :: REqCmdDescr
cmdNewProof
  = ( "N"
    , "new proof"
    , unlines
       [ "N i - start new proof for a conjecture."
       , "i : conjecture number"
       ]
    , doNewProof )

doNewProof args reqs
  = case newProof1 (args2int args) reqs of
     Nothing -> do putStrLn "invalid conjecture number"
                   return reqs
     Just (nconj,strats)
      -> do putStrLn $ numberList presentSeq $ strats
            putStr "Select sequent:- " ; choice <- getLine
            case newProof2 nconj strats (readInt choice) reqs of
             Nothing -> doshow reqs "Invalid strategy no"
             Just liveProof
              -> proofREPL reqs liveProof
\end{code}

\begin{code}
cmdRet2Proof :: REqCmdDescr
cmdRet2Proof
  = ( "r"
    , "return to live proof"
    , unlines
       [ "r i - return to a live proof."
       , "i : optional live proof number"
       , "    - if more than one."
       ]
    , doBack2Proof )

doBack2Proof args reqs
  = case resumeProof (args2int args) reqs of
      Nothing -> do putStrLn "Can't find requested live proof"
                    return reqs
      Just liveProof -> proofREPL reqs liveProof
\end{code}

Presenting a sequent for choosing:
\begin{code}
presentSeq (str,seq)
  = "'" ++ str ++ "':  "
    ++ presentHyp (hyp seq)
    ++ " " ++ _vdash ++ " " ++
    trTerm 0 (cleft seq)
    ++ " = " ++
    trTerm 0 (cright seq)

presentHyp hthy
  = intercalate "," $ map (trTerm 0 . fst . snd . fst) $ laws hthy
\end{code}


\newpage
\subsection{Proof REPL}

We start by defining the proof REPL state:
\begin{code}
type ProofState
  = ( REqState   -- reasonEq state
    , LiveProof )  -- current proof state
\end{code}
From this we can define most of the REPL configuration.
\begin{code}
proofREPLprompt justHelped (_,liveProof)
  | justHelped  =  unlines' [ dispLiveProof liveProof
                            , "proof: "]
  | otherwise   =  unlines' [ clear -- clear screen, move to top-left
                            , dispLiveProof liveProof
                            , "proof: "]

proofEOFReplacement = []

proofREPLParser = charTypeParse

proofREPLQuitCmds = ["q"]

proofREPLQuit args (reqs,liveProof)
  = do putStr "Proof Incomplete, Abandon ? [Y] : "
       hFlush stdout
       inp <- getLine
       if trim inp == "Y"
        then return (True,(abandonProof reqs liveProof, liveProof))
        else return (True,(saveProof reqs liveProof, liveProof))

proofREPLHelpCmds = ["?"]

proofREPLEndCondition (reqs,liveProof)
  =  proofIsComplete (logicsig reqs) liveProof

proofREPLEndTidy _ (reqs,liveProof)
  = do putStrLn "Proof Complete"
       return ( completeProof reqs liveProof, liveProof)
\end{code}

\begin{code}
proofREPLConfig
  = REPLC
      proofREPLprompt
      proofEOFReplacement
      proofREPLParser
      proofREPLQuitCmds
      proofREPLQuit
      proofREPLHelpCmds
      ( map clearLong
            [ listLawDescr
            , goDownDescr
            , goUpDescr
            , matchLawDescr
            , applyMatchDescr
            , flatEquivDescr
            , groupEquivDescr
            , goBackDescr
            , lawInstantiateDescr
            , switchConsequentDescr
            , switchHypothesisDescr
            , leaveHypothesisDescr
            , cloneHypothesisDescr
            ])
      proofREPLEndCondition
      proofREPLEndTidy
\end{code}

This repl runs a proof.
\begin{code}
proofREPL reqs liveProof
 = do (reqs',_) <- runREPL
                       (clear++"Prover starting...")
                       proofREPLConfig
                       (reqs,liveProof)
      return reqs'
\end{code}

We have a common pattern:
try to update a second component of a two-part state,
in a monadic context.
Accept if it suceeds, otherwise no change
\begin{code}
tryDelta :: Monad m => (b -> Maybe b) -> (a,b) -> m (a,b)
tryDelta delta (reqs, liveProof)
  = case delta liveProof of
       Nothing          ->  return (reqs, liveProof )
       Just liveProof'  ->  return (reqs, liveProof')
\end{code}

Listing laws
\begin{code}
listLawDescr = ( "ll", "list laws", "ll -- list all available laws", listLaws)

listLaws :: REPLCmd (REqState, LiveProof)
listLaws _ state@( reqs, _)
  = do putStrLn $ observeLaws reqs
       putStr "<return> to continue..." ; hFlush stdout ; getLine
       return state
\end{code}


Focus movement commands
\begin{code}
goDownDescr = ( "d", "down", "d n  -- down n", goDown )

goDown :: REPLCmd (REqState, LiveProof)
goDown args = tryDelta (moveFocusDown $ args2int args)

goUpDescr = ( "u", "up", "u  -- up", goUp )

goUp :: REPLCmd (REqState, LiveProof)
goUp _ = tryDelta moveFocusUp
\end{code}

Switching consequent focus:
\begin{code}
switchConsequentDescr
  = ( "s", "switch",
      unlines' [ "s  -- switch between C_left/C_right"
               , "   -- or go to C_left if in hypothesis" ]
    , switchConsequent )

switchConsequent :: REPLCmd (REqState, LiveProof)
switchConsequent _ = tryDelta moveConsequentFocus
\end{code}

Switching focus to a hypothesis:
\begin{code}
switchHypothesisDescr
  = ( "h", "to hypothesis"
    , "h i  -- focus on hypothesis i, use 'l' to exit."
    , switchHypothesis )

switchHypothesis :: REPLCmd (REqState, LiveProof)
switchHypothesis args = tryDelta (moveFocusToHypothesis $ args2int args)
\end{code}

Returning focus from a hypothesis:
\begin{code}
leaveHypothesisDescr
  = ( "l", "leave hypothesis"
    , "l  --  leave hypothesis, go to C_left."
    , leaveHypothesis )

leaveHypothesis :: REPLCmd (REqState, LiveProof)
leaveHypothesis _ = tryDelta moveFocusFromHypothesis
\end{code}


\newpage
Law Matching
\begin{code}
matchLawDescr = ( "m", "match laws", "m  -- match laws", matchLawCommand )

matchLawCommand :: REPLCmd (REqState, LiveProof)
matchLawCommand _ (reqs, liveProof)
  =  return (reqs, matchFocus (logicsig reqs) liveProof)
\end{code}

Applying a match.
\begin{code}
applyMatchDescr = ( "a", "apply match"
                  , "a i  -- apply match number i", applyMatch )

applyMatch :: REPLCmd (REqState, LiveProof)
applyMatch args  =  tryDelta (applyMatchToFocus (args2int args))
\end{code}

Flattening grouped equivalences:
\begin{code}
flatEquivDescr = ( "fe", "flatten equivalences"
                 , "flatten= equivalences"
                 , flatEquiv )

flatEquiv :: REPLCmd (REqState, LiveProof)
flatEquiv _ state@(reqs, _)
  = tryDelta (flattenAssociative $ theEqv $ logicsig reqs) state
\end{code}


Re-grouping flattened equivalences:
\begin{code}
groupEquivDescr = ( "ge", "group equivalences"
                  , unlines' [ "ge l -- associate to the left"
                             , "ge r -- associate to the right"
                             , "ge l <n> -- gather first <n>"
                             , "ge r <n> -- gather last <n>"
                             , "ge s <n> -- split at <n>"
                             ]
                  , groupEquiv )

args2gs ["l"]                       =  return $ Assoc Lft
args2gs ["r"]                       =  return $ Assoc Rght
args2gs ("l":as) | args2int as > 0  =  return $ Gather Lft  $ args2int as
args2gs ("r":as) | args2int as > 0  =  return $ Gather Rght $ args2int as
args2gs ("s":as) | args2int as > 0  =  return $ Split       $ args2int as
args2gs _                           =  fail "ge: invalid arguments."

groupEquiv :: REPLCmd (REqState, LiveProof)
groupEquiv args state@(reqs, _)
  = case args2gs args of
      Just gs -> tryDelta (groupAssociative (theEqv $ logicsig reqs) gs) state
      Nothing -> putStrLn "bad arguments!" >> entertogo >> return state
\end{code}

Undoing the previous step (if any)
\begin{code}
goBackDescr = ( "b", "go back (undo)"
              , unlines' [ "b   --- undo last proof step"
                         , "b i --- undo the last 'i' proof steps"
                         , "    --- cannot undo sequent changes yet"]
              , goBack )

goBack :: REPLCmd (REqState, LiveProof)
goBack args  =  tryDelta (stepBack (args2int args))
\end{code}

\newpage
Law Instantiation.
Replacing \textit{true} by a law, with unknown variables
suitably instantiated.
\begin{code}
lawInstantiateDescr = ( "i", "instantiate"
                      , "i  -- instantiate a true focus with an law"
                      , lawInstantiateProof )

lawInstantiateProof :: REPLCmd (REqState, LiveProof)
lawInstantiateProof _ ps@(reqs, liveProof )
  = do let rslaws = lawInstantiate1 (logicsig reqs) liveProof

       lawno <- pickByNumber "Pick a law : " showLaws rslaws

       case lawInstantiate2 rslaws lawno liveProof of
         Nothing -> return ps
         Just (lawt,vs,ts)
           -> do (cancel,vs2ts) <- pickPairing
                   "Chosen law : " (showLaw 0)
                   "Free unknown law variables: " trVar
                   "Goal sub-terms:" (trTerm 0)
                   (\ v-> "Binding for "++trVar v)
                   lawt vs ts
                 if cancel then return (reqs,liveProof)
                 else do
                  liveProof' <- lawInstantiate3 lawt vs2ts liveProof
                  return (reqs, liveProof' )
\end{code}

Hypothesis Cloning, is based on the following law:
\[H \implies C \equiv H \implies H \land C\]
\begin{code}
cloneHypothesisDescr
  = ( "c", "clone hyp", "c i  -- clone hypothesis i"
    , cloneHypotheses )

cloneHypotheses :: REPLCmd (REqState, LiveProof)
cloneHypotheses args liveState@(reqs, _)
  = tryDelta (cloneHypothesis (args2int args) (theAnd $ logicsig reqs)) liveState
\end{code}

\newpage
\subsection{Development Commands}

\subsubsection{Builtin Theory Handling}

\begin{code}
cmdBuiltin :: REqCmdDescr
cmdBuiltin
  = ( "b"
    , "builtin theory handling"
    , unlines
        [ "b "++binExists++" -- list all existing builtin theories"
        , "b "++binInstalled++" -- list all installed theories"
        , "b "++binInstall++" <name> -- install builtin theory <name>"
        ]
    , buildIn )

binExists = "e"
binInstalled = "i"
binInstall = "I"

buildIn (cmd:_) reqs
 | cmd == binExists
    =  doshow reqs (devListAllBuiltins ++ '\n':devBIRemind)
 | cmd == binInstalled
   = doshow reqs $ observeTheoryNames reqs

buildIn (cmd:nm:_) reqs
 | cmd == binInstall
   = do (outcome,reqs') <- devInstallBuiltin reqs nm
        case outcome of
          Just msg -> doshow reqs msg
          Nothing -> return reqs'

buildIn _ reqs = doshow reqs "unrecognised 'b' otion"
\end{code}
