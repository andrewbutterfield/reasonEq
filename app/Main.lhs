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
import System.Directory
import System.Exit
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
import Files

import LexBase
import Variables
import AST
import VarData
import SideCond
import Assertions
import Binding
import REqState
import AbstractUI
import StdSignature(propSignature)
import UTPSignature
import Instantiate
import TestRendering
import TestParsing
import REPL
import Dev

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\newpage

\begin{code}
progName = "reasonEq"
version = "0.8.alpha"
name_version = progName++" "++version
\end{code}

\subsection{\texttt{main}}

The program takes command-line arguments
that tailor its behaviour.
For now, we consider the following behavioural aspects:
\begin{description}
  \item [UI]
    We propose to support both a text-based REPL
    and a graphical user-interface. The REPL is the default,
    while the GUI can be invoked with the \texttt{-g} argument (anywhere).
  \item [FS]
    We allow the specification of where in the filesystem the prover data files
    are kept.
    We support a project-based approach, where a project is simply
    a folder (``workspace'') containing all relevant files.
    We can specify the path to same using the \texttt{-w} command-line option.
    We also have the notion of a single separate folder with global data
    that gives the locations of all known project folders.
    For now this lives in a OS-dependent user-specific location.
    In particular we use a design that allows the program itself
    to setup global configuration data, in an OS-dependent manner.
  \item [Dev]
    We also allow two modes when running: ``User'' \texttt{-u}
    and ``Dev'' \texttt{-d}.
    In User mode, the default, all prover state is loaded from data files,
    as specified by FS above.
    In Dev mode, some prover state may be pre-installed,
    and there may be additional proof commands available.
\end{description}

So we can summarise flags as follows:
\begin{code}
helpFlag        = "-h"
helpLongFlag    = "--help"
versionFlag     = "-v"
versionLongFlag = "--version"

guiFlag        = "-g"    --          use GUI
replFlag       = "-r"    --          use REPL (default)
workspaceFlag  = "-w"    -- <path>   path to prover workspace
userFlag       = "-u"    --          run in 'User' mode
devFlag        = "-d"    --          run in 'Dev' mode
cwdConfig      = ".req"  -- local config file (contains flags)

helpinfo
 = putStrLn $ unlines
     [ "Usage:\n"
     , "req [command-line-options]\n"
--     , option guiFlag "start-up GUI"
     , option replFlag "start-up REPL"
     , option (workspaceFlag++" <dir>") "workspace directory"
     , option userFlag "start-up in User mode (default)"
     , option devFlag "start-up in Dev mode"
     , ""
     , "\t-h, --help \t output this help and exit"
     , "\t-v, --version \t output program version and exit"
--     , ""
--     , "options can also be included in file '.req'"
     ]
 where
   option flag explanation = '\t':flag ++ '\t':explanation
\end{code}

\newpage
We shall define a record to record flag data,
and a corresponding parser:
\begin{code}
data CMDFlags = CMDFlags { usegui  :: Bool
                         , wspath :: Maybe FilePath
                         , dev     :: Bool}

defFlags = CMDFlags { usegui  = False
                    , wspath = Nothing
                    , dev     = False }

parseArgs :: [[Char]] -> CMDFlags
parseArgs args = parse defFlags args where
  parse flags [] = flags
  parse flags (f:p:ss)
   | f == workspaceFlag  =  parse flags{ wspath = checkfp p } ss
   where checkfp fp
           | isValid fp  =  Just fp
           | otherwise   =  Nothing
  parse flags (f:ss)
   | f == guiFlag      =  parse flags{ usegui = True  }   ss
   | f == replFlag     =  parse flags{ usegui = False }   ss
   | f == userFlag     =  parse flags{ dev    = False }   ss
   | f == devFlag      =  parse flags{ dev    = True  }   ss
   -- ignore anything else
   | otherwise         =  parse flags                     ss
\end{code}

\begin{code}
main :: IO ()
main
  = do args <- getArgs
       info args runargs

info args runargs
 | args == [helpFlag]         =  helpinfo
 | args == [helpLongFlag]     =  helpinfo
 | args == [versionFlag]      =  putStrLn name_version
 | args == [versionLongFlag]  =  putStrLn name_version
 | otherwise                  =  runargs args

runargs args
  = do let flags = parseArgs args
       reqs0 <- initState flags
       if usegui flags
       then do putStrLn "starting GUI..."
               gui reqs0
       else do putStrLn "starting REPL..."
               repl reqs0
\end{code}


\newpage
\subsection{Initialising State}

We assume user mode by default.

\begin{code}
initState :: CMDFlags -> IO REqState

initState flags
  = case wspath flags of
      Nothing ->
        if dev flags
        then return $ devInitState
        else do  putStrLn "Running user mode, default initial state."
                 (appFP,projects) <- getWorkspaces progName
                 putStrLn ("appFP = "++appFP)
                 putStrLn ("projects:\n"++unlines projects)
                 (pname,projfp)
                    <- currentWorkspace
                         ( unlines $ fst $ writeREqState reqstate0 )
                                     projects
                 putStrLn ("Project Name: "++pname)
                 putStrLn ("Project Path: "++projfp)
                 putStrLn "Loading..."
                 readAllState projfp
      Just fp ->
        do ok <- doesDirectoryExist fp
           if ok
           then if dev flags
                then return $ devInitState{ projectDir = fp }
                else do putStrLn "Running user mode, loading project state."
                        readAllState fp
           else die ("invalid workspace: "++fp)

reqstate0 = REqState { inDevMode = False
                     , projectDir = ""
                     , modified = False
                     , settings = reqset0
                     , logicsig = propSignature
                     , theories = noTheories
                     , currTheory = ""
                     , liveProofs = M.empty }

reqset0 = REqSet { maxMatchDisplay = 40
                 }
\end{code}

\newpage


\subsection{GUI Top-Level}

The GUI has yet to be developed but will probably
use \texttt{threepenny-gui} along with the Electron browser.
\begin{code}
gui :: REqState -> IO ()
gui reqs0 = do putStrLn "GUI not implemented, using command-line."
               repl reqs0
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
reqPrompt _ reqs = devMk ++ takeBaseName (projectDir reqs)++ "."
                         ++ currTheory reqs
                         ++ chgd ++ "> "
 where
   chgd = if modified reqs then "*" else ""
   devMk = if inDevMode reqs then "\x1f6e0 " else ""

reqEOFreplacmement = [nquit]

reqParser = wordParse

reqQuitCmds = [nquit] ; nquit = "quit"

reqQuit :: REqExit
reqQuit _ reqs
 | inDevMode reqs  =  byeBye
 | modified  reqs  =  saveAndGo reqs
 | otherwise       =  byeBye
 where
   saveAndGo reqs
    = do putStrLn ("Changes made, saving ....")
         writeAllState reqs
         byeBye
   byeBye = putStrLn "\nGoodbye!\n" >> return (True, reqs)

reqHelpCmds = ["?","help"]

reqCommands :: REqCommands
reqCommands = [ cmdShow, cmdSet, cmdNew
              , cmdNewProof, cmdRet2Proof
              , cmdSave, cmdLoad
              , cmdSaveConj, cmdLoadConj
              , cmdAssume, cmdDemote
              , cmdBuiltin ]

-- we don't use these features in the top-level REPL
reqEndCondition _ = False
reqEndTidy _ reqs = return reqs
\end{code}

\newpage

The configuration:
\begin{code}
reqConfig
  = REPLC reqPrompt reqEOFreplacmement reqParser
          reqQuitCmds reqQuit reqHelpCmds
          reqCommands
          reqEndCondition reqEndTidy
\end{code}

Running the REPL:
\begin{code}
repl :: REqState -> IO ()
repl reqs0
  = do runREPL reqWelcome reqConfig reqs0
       return ()

reqWelcome = unlines
 [ "Welcome to the "++progName++" "++version++" REPL"
 , "Type '?' for help."
 ]
\end{code}

We sometimes want to wait:
\begin{code}
waitForReturn :: IO ()
waitForReturn
  = do putStrLn "<return> to continue"
       getLine
       return ()
\end{code}


\newpage
\subsection{Show Command }
\begin{code}
cmdShow :: REqCmdDescr
cmdShow
  = ( shName
    , "show parts of the prover state"
    , unlines
        [ shName++" "++shWork++" -- show workspace info"
        , shName++" "++shSig++" -- show logic signature"
        , shName++" "++shTheories++" -- show theories"
        , shName++" "++shLaws++" -- show laws"
        , shName++" "++shLaws++" -u -- show variable uniqueness"
        , shName++" "++shKnown++" -- show known names"
        , shName++" "++shCurrThry++" -- show 'current' theory"
        , shName++" "++shConj++" -- show current conjectures"
        , shName++" "++shConj++" -u -- show variable uniqueness"
        , shName++" "++shLivePrf++" -- show current (live) proof"
        , shName++" "++shProofs++" -- show completed proofs"
        , shName++" "++shProofs++" <nm> -- show proof transcript for <nm>"
        ]
    , showState )

shName = "sh"
shWork = "w"
shSig = "s"
shTheories = "t"
shLaws = "L"
shKnown = "k"
shCurrThry = "T"
shConj = "c"
shLivePrf = "p"
shProofs = "P"

-- these are not robust enough - need to check if component is present.
showState (cmd:args) reqs
 | cmd == shProofs    =  doshow reqs $ observeCompleteProofs args reqs
 | cmd == shWork      =  showWorkspaces args reqs
 | cmd == shSig       =  doshow reqs $ observeSig reqs
 | cmd == shTheories  =  doshow reqs $ observeTheories reqs
 | cmd == shLaws      =  doshow reqs $ observeLaws reqs args
 | cmd == shKnown     =  doshow reqs $ observeKnowns reqs args
 | cmd == shCurrThry  =  doshow reqs $ observeCurrTheory reqs
 | cmd == shConj      =  doshow reqs $ observeCurrConj reqs args
 | cmd == shLivePrf   =  doshow reqs $ observeLiveProofs reqs
showState _ reqs      =  doshow reqs "unknown 'show' option."

doshow :: REqState -> String -> IO REqState
doshow reqs str  =  putStrLn str >> return reqs


showWorkspaces :: [String] -> REqState -> IO REqState
showWorkspaces args reqs
  = do (appFP,projects) <- getWorkspaces progName
       putStrLn ("Application Data:\n\t"++appFP)
       putStrLn ("Project Folders:\n"++unlines (map ('\t':) projects))
       return reqs
\end{code}

\newpage
\subsection{State Save and Restore}


\begin{code}
cmdSave, cmdLoad :: REqCmdDescr
cmdSave
  = ( "save"
    , "save prover state to file"
    , unlines
        [ "save          -- save all prover state to current workspace"
        , "save .        -- save current theory to current workspace"
        , "save <thry>   -- save theory <thry> to current workspace"]
    , saveState )
cmdLoad
  = ( "load"
    , "load prover state from file"
    , unlines
        [ "load -- load prover state from current workspace"
        , "load <thry> -- load EXISTING theory <thry> from current workspace"
        , "load new <thry> -- add NEW theory <thry> from current workspace"]
    , loadState )

saveState [] reqs
  = do writeAllState reqs
       putStrLn ("REQ-STATE written to '"++projectDir reqs++"'.")
       return reqs{ modified = False }
saveState [nm] reqs
  = let nm' = if nm == "." then (currTheory reqs) else nm
    in
    case getTheory nm' $ theories reqs of
      Nothing
       -> do putStrLn ("No such theory: '"++nm'++"'")
             return reqs
      Just thry
       -> do writeNamedTheoryTxt reqs (nm',writeTheory thry)
             putStrLn ("Theory '"++nm'++"' written to '"++projectDir reqs++"'.")
             return reqs
saveState _ reqs  =  doshow reqs "unknown 'save' option."

loadState [] reqs
  = do let dirfp = projectDir reqs
       putStrLn ("Reading all prover state from "++dirfp++"...")
       reqs' <- readAllState dirfp
       putStrLn ("...done.")
       return reqs'{ inDevMode = inDevMode reqs}
loadState [nm] reqs
  = do let dirfp = projectDir reqs
       (nm,thry) <- readNamedTheory dirfp nm
       putStrLn ("Theory '"++nm++"'read from  '"++projectDir reqs++"'.")
       return $ changed $ theories__ (replaceTheory' thry) reqs
loadState ["new",nm] reqs
  = do let dirfp = projectDir reqs
       (nm,thry) <- readNamedTheory dirfp nm
       putStrLn ("Theory '"++nm++"'read from  '"++projectDir reqs++"'.")
       case addTheory thry $ theories reqs of
         Yes thrys' -> return $ changed $ theories_ thrys' reqs
         But msgs ->
           do putStrLn ("Add theory failed:\n"++unlines' msgs)
              return reqs
loadState _ reqs  =  doshow reqs "unknown 'load' option."
\end{code}

\newpage
\subsection{Conjecture Management}

\begin{code}
cmdSaveConj :: REqCmdDescr
cmdSaveConj
  = ( "svc"
    , "save conjectures"
    , unlines
        [ "svc -- save all laws in current theory as conjectures"
        ]
    , saveConjectures )

saveConjectures _ reqs
  = case getTheory (currTheory reqs) $ theories reqs of
      Nothing
       -> do putStrLn ("Can't find current theory!!!\BEL")
             return reqs
      Just thry
       -> do let lawConjs = map lawNamedAssn (laws thry)
             let allConjs = lawConjs ++ conjs thry
             putStrLn $ unlines' $ map show allConjs
             writeConjectures reqs (thName thry) allConjs
             return reqs
\end{code}

\begin{code}
cmdLoadConj :: REqCmdDescr
cmdLoadConj
  = ( "ldc"
    , "load conjectures"
    , unlines
        [ "ldc <nm> -- display conjectures in <nm>.cnj "
        , "         -- proper loading to be implemented later, as needed."
        ]
    , displayConjectures )

displayConjectures [nm] reqs
  = do savedConjs <- readFiledConjectures (projectDir reqs) nm
       putStrLn $ unlines' $ map (trNmdAsn) savedConjs
       return reqs
displayConjectures _ reqs  =  doshow reqs "unknown 'ldc' option."
\end{code}


\newpage
\subsection{Set Command}
\begin{code}
cmdSet :: REqCmdDescr
cmdSet
  = ( "set"
    , "set parts of the prover state"
    , unlines
        [ "set "++setCurrThry++" 'name' -- set current theory to 'name'"
        ]
    , setState )

setCurrThry = shCurrThry

setState (cmd:rest) reqs
 | cmd == setCurrThry
    =  case setCurrentTheory nm reqs of
         Nothing     ->  doshow reqs  ("No such theory: '"    ++ nm ++ "'")
         Just reqs'  ->  doshow reqs' ("Current Theory now '" ++ nm ++ "'")
 where nm = args2str rest
setState _ reqs      =  doshow reqs "unknown 'set' option."
\end{code}

\subsection{New Command}
\begin{code}
cmdNew :: REqCmdDescr
cmdNew
  = ( "new"
    , "generate new theory items"
    , unlines
        [ "new "++shConj++" 'np1' .. 'npk' -- new conjecture 'np1-..-npk'"]
    , newThing )

newThing (cmd:rest) reqs
 | cmd == shConj = newConj rest reqs
newThing _ reqs      =  doshow reqs "unknown 'new' option."
\end{code}

New Conjecture:
\begin{code}
newConj args reqs
  = do let cjnm = mkLawName args
       putStr ("New conj, '"++cjnm++"', enter term :- ")
       hFlush stdout; trtxt <- getLine
       case sPredParse trtxt of
         But msgs  -> doshow reqs ("Bad Term, "++unlines' msgs)
         Yes (term,_) ->
          case newConjecture (currTheory reqs) (cjnm,(mkAsn term scTrue)) reqs
          of
            But msgs  -> doshow reqs (unlines' msgs)
            Yes reqs' -> do putStrLn ("Conjecture '"++cjnm++"' installed")
                            return reqs'
\end{code}

\newpage
\subsection{Faking It}

Simply assuming conjectures as laws:
\begin{code}
cmdAssume :: REqCmdDescr
cmdAssume
  = ( "Assume"
    , "assume conjecture is law"
    , unlines
       [ "Assume n - assume conjecture 'n'"
       , "Assume * - assume all current theory conjectures"
       ]
    , doAssumption )

doAssumption args reqs
  =  case assumeConjecture (currTheory reqs) cjnm reqs of
         But lns     ->  doshow reqs  (unlines' lns)
         Yes reqs'  ->  doshow reqs' ("Assumed " ++ cjnm)
 where cjnm = args2str args
\end{code}


Reverting proven or assumed laws back to conjectures.
\begin{code}
cmdDemote :: REqCmdDescr
cmdDemote
  = ( "Demote"
    , "demote law to conjectures"
    , unlines
       [ "Demote n - demote law 'n'"
       , "Demote [] - demote all current theory proven laws"
       , "Demote * - demote all current theory assumed laws"
       ]
    , doDemotion )

doDemotion args reqs
  =  case demoteLaw (currTheory reqs) lwnm reqs of
         But lns     ->  doshow reqs  (unlines' lns)
         Yes reqs'  ->  doshow reqs' ("Demoted " ++ lwnm)
 where lwnm = args2str args
\end{code}


\newpage
\subsection{Proving Commands}


Then we introduce doing a proper proof:
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
            putStr "Select sequent by number: "
            hFlush stdout
            choice <- getLine
            case newProof2 nconj strats (readInt choice) reqs of
             Nothing -> doshow reqs "Invalid strategy no"
             Just liveProof -> proofREPL reqs liveProof
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
    ++ "   " ++ _vdash ++ "   " ++
    trTerm 0 (cleft seq)
    ++ "   =   " ++
    trTerm 0 (cright seq)

presentHyp hthy
  = intercalate "," $ map (trTerm 0 . assnT . snd . fst) $ laws hthy
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
            [ listScopeLawsDescr
            , listScopeKnownsDescr
            , goDownDescr
            , goUpDescr
            , matchLawDescr
            , tryMatchDescr
            , applyMatchDescr
            , normQuantDescr
            , simpNestDescr
            , substituteDescr
            , flatEquivDescr
            , groupEquivDescr
            , goBackDescr
            , lawInstantiateDescr
            , switchConsequentDescr
            , switchHypothesisDescr
            , leaveHypothesisDescr
            , cloneHypothesisDescr
            , equivaleStepsDescr
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
Accept if it succeeds, otherwise no change
\begin{code}
tryDelta :: Monad m => (b -> Maybe b) -> (a,b) -> m (a,b)
tryDelta delta pstate@(reqs, liveProof)
  = case delta liveProof of
       Nothing          ->  return pstate
       Just liveProof'  ->  return (reqs, liveProof')
\end{code}

Listing laws in scope for the current live proof.
\begin{code}
listScopeLawsDescr = ( "ll", "list laws"
                     , "ll -- list all laws in scope", listScopeLaws)

listScopeLaws :: REPLCmd (REqState, LiveProof)
listScopeLaws _ state@( _, liveProof)
  = do putStrLn $ observeLawsInScope liveProof
       userPause
       return state
\end{code}

Listing knowns in scope for the current live proof.
\begin{code}
listScopeKnownsDescr = ( "lk", "list knowns"
                     , "lk -- list all known names in scope", listScopeKnowns)

listScopeKnowns :: REPLCmd (REqState, LiveProof)
listScopeKnowns _ state@( reqs, liveProof)
  = do putStrLn $ observeKnownsInScope liveProof
       userPause
       return state
\end{code}

Focus movement commands
\begin{code}
goDownDescr = ( "d", "down", "d n  -- down n, n=1 if ommitted", goDown )

goDown :: REPLCmd (REqState, LiveProof)
goDown args = tryDelta (moveFocusDown $ args2int args)

goUpDescr = ( "u", "up", "u  -- up", goUp )

goUp :: REPLCmd (REqState, LiveProof)
goUp _ = tryDelta moveFocusUp
\end{code}

Switching consequent focus:
\begin{code}
switchConsequentDescr
  = ( "S", "switch",
      unlines' [ "S  -- switch between C_left/C_right"
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
matchLawDescr = ( "m"
                , "match laws"
                , unlines
                   [ "m       -- match all laws"
                   , "m lawnm -- match law 'lawnm'" ]
                , matchLawCommand )

matchLawCommand :: REPLCmd (REqState, LiveProof)
matchLawCommand [] (reqs, liveProof)
  =  return (reqs, matchFocus (logicsig reqs) liveProof)
matchLawCommand args state@(reqs, liveProof)
  =  case matchFocusAgainst lawnm (logicsig reqs) liveProof of
      Yes liveProof'  ->  return (reqs, liveProof')
      But msgs
       -> do putStrLn $ unlines' msgs
             waitForReturn
             return (reqs, matches_ [] liveProof)
  where lawnm = filter (not . isSpace) $ unwords args
\end{code}

Try matching focus against a specific law, to see what outcome arises
\begin{code}
tryMatchDescr = ( "tm"
                , "try match focus"
                , unlines
                   [ "tm             -- try match focus..."
                   , "tm nm          -- ... against law 'nm'"
                   , "tm n1 .. nk nm -- ... against parts n1..nk of law"
                   , "               --     n1..nk :  numbers of parts"
                   , "-- the n1..nk need not be in increasing order"
                   , "-- parts returned in same order as n1..nk"
                   ]
                , tryMatch)

tryMatch :: REPLCmd (REqState, LiveProof)
tryMatch [] state = return state
tryMatch args state@( reqs, liveProof)
  = do case tryFocusAgainst lawnm parts (logicsig reqs) liveProof of
         Yes (bind,tPasC,scP',scP'')
           -> putStrLn $ unlines
                [ banner
                , "Binding: " ++ trBinding bind
                -- , "Replacement: " ++ trTerm 0 repl
                -- , "Unbound: " ++ trVSet (findUnboundVars bind repl)
                , "Instantiated Law = " ++ trTerm 0 tPasC
                , "Instantiated Law S.C. = " ++ trSideCond scP'
                , "Goal S.C. = " ++ trSideCond (conjSC liveProof)
                , "Discharged Law S.C. = " ++ trSideCond scP'']
         But msgs -> putStrLn $ unlines' ( (banner ++ " failed!") : msgs )
       userPause
       return state
  where
    (nums,rest) = span (all isDigit) args
    parts = map read nums
    lawnm = filter (not . isSpace) $ unwords rest
    banner = "Match against `"++lawnm++"'"++show parts
\end{code}

\newpage
Applying a match.
\begin{code}
applyMatchDescr = ( "a", "apply match"
                  , "a i  -- apply match number i", applyMatch )

applyMatch :: REPLCmd (REqState, LiveProof)
applyMatch args pstate@(reqs, liveProof)
  = case applyMatchToFocus1 (args2int args) liveProof of
      Nothing -> return pstate
      Just (unbound,mtch)
       -> do ubind <- completeUnbound unbound mtch
             case applyMatchToFocus2 mtch unbound ubind liveProof of
               Yes liveProof' -> return(reqs, liveProof')
               But msgs
                -> do putStrLn $ unlines msgs
                      waitForReturn
                      return pstate
  where
    true   =  theTrue  $ logicsig reqs
    false  =  theFalse $ logicsig reqs

    completeUnbound unbound mtch
      | S.null unbound  =  return $ mBind mtch
      | otherwise
          = do putStrLn
                $ unlines [ "unbound = " ++ trVSet unbound
                          , "bind = " ++ trBinding (mBind mtch)
                          , "please supply bindings as requested"
                          ]
               requestBindings (true,false)
                               (assnT $ conjecture liveProof) unbound
\end{code}

For every unbound pattern variable in the replacement,
we ask the user to pick from a list of terms:
\begin{code}
requestBindings :: (Term, Term) -> Term -> Set GenVar -> IO Binding
requestBindings (t,f) goalTerm unbound
  = let

      terms = t : f : subTerms goalTerm
      termLen = length terms
      termMenu = numberList (trTerm 0) terms

      gvars = S.toList $ mentionedVars goalTerm
      gvarLen = length gvars
      gvarMenu = numberList trGVar gvars

      lvarPrompt = unlines' [ "numbers separated by spaces"
                            , "enter > "
                            ]

      vlists :: [VarList]
      vlists    = mentionedVarLists goalTerm
                  ++ map S.toList (mentionedVarSets goalTerm)
                  ++ map (:[]) (S.toList unbound)
      vlistLen  = length vlists
      vlistMenu = numberList trVList vlists

      -- we count from 1 !
      inrange upper i = 0 < i && i <= upper

      getFrom1 list i = list!!(i-1)

      rB ubind [] = do putStrLn ("Done: " ++ trBinding ubind)
                       userPause
                       return ubind

      rB ubind gvs@(StdVar v : gvs')
        = do putStrLn ("bindings so far: "++trBinding ubind)
             putStrLn termMenu
             putStrLn ("unbound "++trVar v)
             response <- fmap readInt $ userPrompt "Choose term by number: "
             handleVarResponse ubind gvs v gvs' response


      rB ubind gvs@(LstVar lv : gvs')
        = do putStrLn ("bindings so far: "++trBinding ubind)
             -- putStrLn ("var-lists: " ++ seplist " " trVList vlists)
             -- putStrLn ("var-sets:  " ++ seplist " " trVSet vsets)
             putStrLn vlistMenu
             putStrLn ("unbound "++trLVar lv)
             responseBits <- fmap (map readInt . words) $ userPrompt lvarPrompt
             handleLVarResponse ubind gvs lv gvs' $ nub responseBits

      handleVarResponse ubind gvs v gvs' response
       = if inrange termLen response
         then case bindVarToTerm v (terms!!(response-1)) ubind of
               Nothing      ->  putStrLn "bind var failed" >> return ubind
               Just ubind'  ->  rB ubind' gvs'
         else rB ubind gvs

      handleLVarResponse ubind gvs lv gvs' ixs -- just do one for now
       = if all (inrange vlistLen) ixs
         then do let myvlist = concat $ map (getFrom1 vlists) ixs
                 case bindLVarToVList lv myvlist ubind of
                   Nothing      ->  putStrLn "bind lvar failed"
                                    >> userPause >> return ubind
                   Just ubind'  ->  rB ubind' gvs'
         else rB ubind gvs

    in rB emptyBinding $ S.toList unbound
\end{code}

\newpage
Normalise Quantifiers
\begin{code}
normQuantDescr = ( "nq"
                 , "normalise quantifiers"
                 , unlines
                    [ "n       -- normalise quantifiers" ]
                 , normQuantCommand )

normQuantCommand :: REPLCmd (REqState, LiveProof)
normQuantCommand _ state@(reqs, liveProof)
  =  case normQuantFocus (theories reqs) liveProof of
      Yes liveProof'  ->  return (reqs, liveProof')
      But msgs
       -> do putStrLn $ unlines' msgs
             waitForReturn
             return (reqs, matches_ [] liveProof)
\end{code}

\newpage
Simplify Nested Quantifiers
\begin{code}
simpNestDescr = ( "n"
                , "nest Q simplify"
                , unlines
                   [ "n       -- simplify nested (similar) quantifiers" ]
                , simpNestCommand )

simpNestCommand :: REPLCmd (REqState, LiveProof)
simpNestCommand _ state@(reqs, liveProof)
  =  case nestSimpFocus (theories reqs) liveProof of
      Yes liveProof'  ->  return (reqs, liveProof')
      But msgs
       -> do putStrLn $ unlines' msgs
             waitForReturn
             return (reqs, matches_ [] liveProof)
\end{code}

\newpage
Perform Substitution
\begin{code}
substituteDescr = ( "s"
                , "substitute"
                , unlines
                   [ "s       -- perform substitution" ]
                , substituteCommand )

substituteCommand :: REPLCmd (REqState, LiveProof)
substituteCommand _ state@(reqs, liveProof)
  =  case substituteFocus (theories reqs) liveProof of
      Yes liveProof'  ->  return (reqs, liveProof')
      But msgs
       -> do putStrLn $ unlines' msgs
             waitForReturn
             return (reqs, matches_ [] liveProof)
\end{code}


\newpage
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
      Nothing -> putStrLn "bad arguments!" >> userPause >> return state
\end{code}

Undoing the previous step (if any)
\begin{code}
goBackDescr = ( "b", "go back (undo)"
              , unlines' [ "b   --- undo last proof step"
                         , "    --- cannot undo clone changes yet"]
              , goBack )

goBack :: REPLCmd (REqState, LiveProof)
goBack args  =  tryDelta (stepBack (args2int args))
\end{code}

\newpage
Law Instantiation.
Replacing \textit{true} by a law, with unknown variables
suitably instantiated.
\textbf{
Ideally this should replace the focus $F$ (any focus)
by itself conjoined with the instantiation of any law $L$
($P(F)=P(F \land L)$)
}
\begin{code}
lawInstantiateDescr = ( "i", "instantiate"
                      , "i  -- instantiate a true focus with an law"
                      , lawInstantiateProof )

lawInstantiateProof :: REPLCmd (REqState, LiveProof)
lawInstantiateProof _ ps@(reqs, liveProof )
  = do let rslaws = lawInstantiate1 (logicsig reqs) liveProof

       lawno <- pickByNumber "Pick a law : " (showLaws (trTerm 0, trSideCond)) rslaws

       case lawInstantiate2 rslaws lawno liveProof of
         Nothing -> return ps
         Just (lawt,vs,ts)
           -> do (cancel,vs2ts) <- pickPairing
                   "Chosen law : " (showLaw (trTerm 0, trSideCond) 0)
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

At any point in a proof, one at least one step has been taken,
we can create a new theorem simply by equivaling the first and last predicates
in the proof. We can then continue with the proof we have got.
In fact, we can create a theorem that equivales any two predicates
within the proof.
\begin{code}
equivaleStepsDescr
  = ( "=", "equivale theorem", "= nm  -- step0 == curr-step 'nm'"
    , equivaleSteps )

equivaleSteps :: REPLCmd (REqState, LiveProof)
equivaleSteps [] liveState
 = do putStrLn ("equivale theorem - name required")
      userPause
      return liveState
equivaleSteps args liveState@(reqs, _)
  = do (outcome,liveState') <- stepEquivalenceTheorem lawnm liveState
       case outcome of
         Just msg  ->  do putStrLn msg
                          userPause
                          return liveState
         Nothing  ->   do putStrLn ("Equivalence law '"++lawnm++"' created.")
                          userPause
                          return liveState'
  where lawnm = filter (not . isSpace) $ unwords args
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
        , "           -- fails if theory already installed"
        , "b "++binReset++" <name> -- reset builtin theory <name>"
        , "           -- replaces already installed theory by builtin version"
        , "                                        (a.k.a. 'factory setting')"
        , "b "++binUpdate++" <name> -- update builtin theory <name>"
        , "           -- adds in new material from builtin version"
        , "           -- asks user regarding revisions to existing material"
        , "b "++binUForce++" <name> -- force-update builtin theory <name>"
        , "           -- adds in new and revised material from builtin version"
        , "           -- does not ask user to confirm revisions"
        ]
    , buildIn )

binExists = "e"
binInstalled = "i"
binInstall = "I"
binReset = "R"
binUpdate = "U"
binUForce = "F"

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

 | cmd == binReset
   = do (outcome,reqs') <- devResetBuiltin reqs nm
        case outcome of
          Just msg -> doshow reqs msg
          Nothing -> return reqs'

 | cmd == binUpdate
   = do (outcome,reqs') <- devUpdateBuiltin reqs nm False
        case outcome of
          Just msg -> doshow reqs msg
          Nothing -> return reqs'

 | cmd == binUForce
   = do (outcome,reqs') <- devUpdateBuiltin reqs nm True
        case outcome of
          Just msg -> doshow reqs msg
          Nothing -> return reqs'

buildIn _ reqs = doshow reqs "unrecognised 'b' option"
\end{code}
