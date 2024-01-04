\chapter{Main Program}
\begin{verbatim}
Copyright (c) Andrew Buttefield 2017--24
              Saqid Zardari     2023
              Aaron Bruce       2023

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

import Symbols hiding (help)

import YesBut
import Utilities
import StratifiedDAG
import Persistence

import LexBase
import Variables
import AST
import VarData
import Binding
import Typing
import SideCond
import Assertions
import Ranking
import REqState
import AbstractUI
import UTPSignature
import Instantiate
import TestRendering
import TestParsing
import REPL
import Dev
import SAT
import Classifier
import LiveProofs

import Debugger
\end{code}

\newpage

\begin{code}
progName = "reasonEq"
version = "0.8.0.0"
name_version = progName++" "++version
\end{code}

\section{\texttt{main}}

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
\section{Initialising State}

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
                 putStrLn ("projects:\n"++(unlines $ map show projects))
                 (ok,pname,projfp) <- currentWorkspace projects
                 putStrLn ("Project Name: "++pname)
                 putStrLn ("Project Path: "++projfp)
                 putStrLn "Loading..."
                 readAllState reqstate0 projfp
      Just fp ->
        do ok <- doesDirectoryExist fp
           if ok
           then if dev flags
                then return $ devInitState{ projectDir = fp }
                else do putStrLn "Running user mode, loading project state."
                        readAllState reqstate0 fp
           else die ("invalid workspace: "++fp)

reqstate0 = REqState { inDevMode = False
                     , projectDir = ""
                     , modified = False
                     , settings = initREqSettings
                     , theories = noTheories
                     , currTheory = ""
                     , liveProofs = M.empty }
\end{code}

\newpage


\section{GUI Top-Level}

The GUI has yet to be developed but will probably
use \texttt{threepenny-gui} along with the Electron browser.
\begin{code}
gui :: REqState -> IO ()
gui reqs0 = do putStrLn "GUI not implemented, using command-line."
               repl reqs0
\end{code}

\newpage
\section{REPL Top-Level}

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
              , cmdBuiltin
              , cmdClassify ]

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


\newpage
\section{Show Command }
\begin{code}
cmdShow :: REqCmdDescr
cmdShow
  = ( shName
    , "show parts of the prover state"
    , unlines
        [ shName++" "++shWork++" -- show workspace info"
        , shName++" "++shSettings++" -- show settings"
        , shName++" "++shSig++" -- show logic signature"
        , shName++" "++shTheories++" -- show theories"
        , shName++" "++shLaws++" -- show laws"
        , shName++" "++shLaws++" -u -- show variable uniqueness"
        , shName++" "++shKnown++" -- show known names"
        , shName++" "++shCurrThry++" -- show 'current' theory"
        , shName++" "++shConj++" -- show current conjectures"
        , shName++" "++shConj++" -u -- show variable uniqueness"
        , shName++" "++shLivePrf++" -- show current (live) proof"
        , shName++" "++shProofs++" -- show completed theory proofs"
        , shName++" "++shProofs++" * -- show all completed proofs"
        , shName++" "++shProofs++" <nm> -- show proof transcript for <nm>"
        ]
    , showState )

shName = "sh"
shWork = "w"
shSettings = "X"
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
 | cmd == shSettings  =  doshow reqs $ observeSettings reqs
showState _ reqs      =  doshow reqs "unknown/unimplemented 'show' option."

doshow :: REqState -> String -> IO REqState
doshow reqs str  =  putStrLn str >> return reqs


showWorkspaces :: [String] -> REqState -> IO REqState
showWorkspaces args reqs
  = do (appFP,projects) <- getWorkspaces progName
       putStrLn ("Application Data:\n\t"++appFP)
       putStrLn ("Project Folders:\n"++unlines (map (('\t':) . thd3) projects))
       return reqs
\end{code}

\newpage
\section{State Save and Restore}

We save and load theories by default,
but can also handle smaller objects such as axioms, conjetures, and proofs.
\begin{code}
prfObj = "prf"
\end{code}


\begin{code}
cmdSave :: REqCmdDescr
cmdSave
  = ( "save"
    , "save prover state to file"
    , unlines
        [ "save          -- save all prover state to current workspace"
        , "save .        -- save current theory to current workspace"
        , "save <thry>   -- save theory <thry> to current workspace"
        , "save " ++ prfObj
                  ++" <proof>  -- save proof <proof> to current workspace"
        , "To come:"
        , "save cnj <conj>  -- save conjecture <cnj> to current workspace"
        , "save ax <axiom>  -- save axiom <axiom> to current workspace"
        ]
    , saveState )

saveState [] reqs = writeAllState reqs
saveState [nm] reqs
  = let nm' = if nm == "." then (currTheory reqs) else nm
    in
    case getTheory nm' $ theories reqs of
      Nothing
       -> do putStrLn ("No such theory: '"++nm'++"'")
             return reqs
      Just thry
       -> do writeNamedTheory (projectDir reqs) (nm',thry)
             return reqs
saveState [what,nm] reqs
  | what == prfObj  
      = case ( getTheory (currTheory reqs) (theories reqs) 
               >>= find (pnm nm) . proofs
             ) of
          Nothing 
            ->  do  putStrLn ("No such proof: '"++nm++"'")
                    return reqs
          Just prf 
            ->  do  writeProof reqs nm prf
                    putStrLn ("Proof '"++nm++"' saved")
                    return reqs
  where pnm nm (pn,_,_,_) = nm == pn
saveState _ reqs  =  doshow reqs "unknown 'save' option."
\end{code}

\newpage

\begin{code}
cmdLoad :: REqCmdDescr
cmdLoad
  = ( "load"
    , "load prover state from file"
    , unlines

        [ "load -- load prover state from current workspace"
        , "load <thry> -- load theory <thry> from current workspace"
        , "            -- warns if it modifies an existing theory"
        , "load " ++ prfObj 
                  ++ " <proof>  -- load proof <proof> to current workspace"
        , "To come:"
        , "load cnj <conj>  -- load conjecture <cnj> to current workspace"
        , "load ax <axiom>  -- load axiom <axiom> to current workspace"
        ]
    , loadState )

loadState [] reqs
  = do let dirfp = projectDir reqs
       reqs' <- readAllState reqs dirfp
       return reqs'{ inDevMode = inDevMode reqs}
loadState [nm] reqs
  = do let dirfp = projectDir reqs
       (ok,old,theories') <- readNamedTheory (theories reqs) dirfp nm
       if ok
        then ( if old
               then do putStr "keep change? (y/N)? "
                       hFlush stdout
                       response <- fmap trim $ getLine
                       if take 1 response == "y"
                       then return $ changed $ theories_ theories' reqs
                       else return reqs
               else return $ changed $ theories_ theories' reqs )
        else return reqs
       
loadState [what,nm] reqs
  | what == prfObj
    = do result <- readProof dirfp nm
         case result of
           Nothing -> return reqs
           Just prf -> do putStrLn ("Loaded:\n"++show prf++"\n Not Yet Stored")
                          return reqs
  where dirfp = projectDir reqs

-- addTheoryProof :: String -> Proof -> Theories -> Theories
-- addTheoryProof thname prf thrys

loadState _ reqs  =  doshow reqs "unknown 'load' option."
\end{code}

\newpage
\section{Conjecture Management}

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

\section{Classify Command}
\begin{code}
cmdClassify :: REqCmdDescr
cmdClassify
  = ( "classify"
    , "activate classifier"
    , unlines 
       [ "classify n - classify law 'n'"
       , "classify . - classify all current theory laws"
       , "classify * - classify all dependency theory laws"
       ]
    , doClassify)

doClassify args reqs
  =  case classifyLaw (currTheory reqs) lwnm reqs of
         But lns     ->  doshow reqs  (unlines' lns)
         Yes reqs'   ->  doshow reqs' ("Classify " ++ lwnm)
 where lwnm = args2str args

\end{code}

\newpage
\section{Set Command}
\begin{code}
cmdSet :: REqCmdDescr
cmdSet
  = ( "set"
    , "set parts of the prover state"
    , unlines
        ( [ "set "++setCurrThry++" 'name' -- set current theory to 'name'"
          , "set "++setSettings++" 'setting' 'value' -- set setting=value"
          ]
          ++ map (("      "++) .showSettingStrings) rEqSettingStrings
          ++ ["  e.g. set X mmd 42"]
        )
    , setState )

setCurrThry = shCurrThry
setSettings = shSettings

setState (cmd:rest) reqs
 | cmd == setCurrThry
    =  case setCurrentTheory nm reqs of
         But msgs   ->  doshow reqs $ unlines' msgs
         Yes reqs'  ->  doshow reqs' ("Current Theory now '" ++ nm ++ "'")
 | cmd == setSettings
    =  case modifySettings rest reqs of
         But msgs    ->  doshow reqs $ unlines' msgs
         Yes reqs'  ->  doshow reqs' ("Settings updated")
 where nm = args2str rest
setState _ reqs      =  doshow reqs "unknown/unimplemented 'set' option."
\end{code}

\section{New Command}
\begin{code}
cmdNew :: REqCmdDescr
cmdNew
  = ( "new"
    , "generate new prover items"
    , unlines
        ( [ "new "++shWork++" nm /absdirpath -- new workspace"
          , "       -- do not use '~' or environment variables"
          , "new "++shConj++" 'np1' .. 'npk' -- new conjecture 'np1-..-npk'"
          ] ++ s_syntax )
    , newThing )

newThing cmdargs@[cmd,nm,fp] reqs
 | cmd == shWork = newWorkspace nm fp reqs
newThing (cmd:rest) reqs
 | cmd == shConj = newConj rest reqs
newThing _ reqs      =  doshow reqs "unknown 'new' option."
\end{code}

\newpage

New WorkSpace:
\begin{code}
newWorkspace wsName wsPath reqs
  = if '~' `elem` wsPath || '$' `elem` wsPath || take 1 wsPath /= "/"
    then doshow reqs $ unlines'
           [ "Absolute path required"
           , "Cannot use '~' or environment variables" ]
    else do  putStrLn ("Creating workspace '"++wsName++"' at "++wsPath++"/")
             let newReqs = projectDir_ wsPath reqstate0
             createWorkspace wsName newReqs
             (usfp,wss) <- getWorkspaces progName
             putWorkspaces progName ((False,wsName,wsPath):wss)
             putStrLn ("New workspace recorded at "++usfp)
             return reqs
\end{code}

\newpage

New Conjecture:
\begin{code}
newConj args reqs
  = do  let cjnm = mkLawName args
        let prompt = unlines' s_syntax 
                     ++ "New conj, '"++cjnm++"', enter term :- "
        let preview = trTerm 0
        (ok,term) <- getConfirmedObject prompt parse preview
        if ok
          then 
            do  asn' <- mkAsn term scTrue
                case newConjecture 
                      (currTheory reqs) (cjnm,asn') reqs of
                  But msgs  -> doshow reqs (unlines' msgs)
                  Yes reqs' -> 
                    do putStrLn ("Conjecture '"++cjnm++"' installed")
                       return reqs'
          else return reqs

  where
    parse txt =
      case sPredParse txt of
        But msgs      ->  But msgs
        Yes (term,_)  ->  Yes term
\end{code}
                  

\newpage
\section{Faking It}

Simply assuming conjectures as laws:
\begin{code}
cmdAssume :: REqCmdDescr
cmdAssume
  = ( "Assume"
    , "assume conjecture is law"
    , unlines
       [ "Assume n - assume conjecture 'n'"
       , "Assume . - assume all current theory conjectures"
       , "Assume * - assume all dependency theory conjectures"
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
\section{Proving Commands}


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
      -> do putStrLn "Select proof strategy:"
            putStrLn $ numberList presentSeq $ strats
            putStr "Select sequent by number: "
            hFlush stdout
            choice <- getLine
            case newProof2 nconj strats (readNat choice) reqs of
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
    ++ trTerm 0 (cleft seq)
    ++ strdir str
    ++ trTerm 0 (cright seq)
  where
    
presentHyp hthy
  | null hstring  = ""
  | otherwise =  hstring ++ "  " ++ _vdash ++ "    "
  where
    hstring  = intercalate "," $ map (trTerm 0 . assnT . snd . fst) $ laws hthy

strdir str
  | str == reduceBoth  =  "  --> ? <--  "
  | otherwise          =  "     -->     "
\end{code}


\newpage
\section{Proof REPL}

We start by defining the proof REPL state:
\begin{code}
type ProofState
  = ( REqState   -- reasonEq state
    , LiveProof )  -- current proof state
\end{code}
From this we can define most of the REPL configuration.
\begin{code}
proofREPLprompt justHelped (reqs,liveProof)
  | justHelped  =  unlines' [ dispLiveProof maxm liveProof
                            , "proof: "]
  | otherwise   =  unlines' [ clear -- clear screen, move to top-left
                            , dispLiveProof maxm liveProof
                            , "proof: "]
  where maxm = maxMatchDisplay $ settings reqs

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
  =  proofIsComplete liveProof

proofREPLEndTidy _ (reqs,liveProof)
  = do putStrLn $ dispEndProof liveProof
       putStrLn "Proof Complete"
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
            , goBackDescr
            , matchLawDescr
            , applyMatchDescr
            -- , testDescr
            , normQuantDescr
            , simpNestDescr
            , substituteDescr
            , showProofSettingsDescr
            , modPrfSettingsDescr
            , flatEquivDescr
            , groupEquivDescr
            , lawInstantiateDescr
            , applySATDescr
            , autoDescr
            , switchConsequentDescr
            , switchHypothesisDescr
            , leaveHypothesisDescr
            , cloneHypothesisDescr
            , equivaleStepsDescr
            , tryMatchDescr
            , tryAlphaDescr
            , showMatchesDescr -- dev mode!
            ])
      proofREPLEndCondition
      proofREPLEndTidy
\end{code}

This repl runs a proof.
\begin{code}
proofREPL reqs liveProof
 = do (reqs',_) <- runREPL
                       (clear++"Prover starting...\n"++ observeSettings reqs)
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
switchConsequent _ = tryDelta switchConsequentFocus
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
Auto Proof
\begin{code}
autoDescr = ( "au"
            , "auto proof"
            , unlines
                [ "au -- auto proof simp"
                , "au c -- auto proof comp"
                , "au f -- auto proof fold"
                , "au u -- auto proof unfold"]
            , autoCommand )

autoCommand :: REPLCmd (REqState, LiveProof)
autoCommand args state@(reqs, liveProof)
   = case getTheory (currTheory reqs) $ theories reqs of
      Nothing
       -> do putStrLn ("Can't find current theory!!!\BEL")
             return (reqs, liveProof)
      Just thry
       -> do let autos = allAutos thry $ theories reqs
             case whichApply input of
              True ->  case applyFolds' input autos (reqs, liveProof) of
                          Yes liveProof' -> return (reqs, liveProof')
                          But nothing -> do putStrLn ("No successful matching fold applys")
                                            return (reqs, liveProof)
              False -> do let f = if input == "c" then checkIsComp else checkIsSimp
                          case applySimps' f autos (reqs, liveProof) of
                              Yes liveProof' -> return (reqs, liveProof')
                              But nothing -> do putStrLn ("No successful matching simp applys")
                                                return (reqs, liveProof)
    where
      input = unwords args

whichApply :: String -> Bool
whichApply "f" = True
whichApply "u" = True
whichApply _ = False

allAutos :: Theory -> Theories -> AutoLaws
allAutos thry thys = do let depthys = getTheoryDeps' (thName thry) thys
                        combineAutos nullAutoLaws ((depAutos [] depthys) ++ [auto thry])

depAutos :: [AutoLaws] -> [Theory] -> [AutoLaws]
depAutos autos [] = autos
depAutos autos (depthy:depthys) = depAutos (autos ++ [auto depthy]) depthys

applySimps' :: MonadFail m => ((String, Direction) -> MatchClass -> Bool) -> 
                              AutoLaws -> (REqState, LiveProof) -> m LiveProof
applySimps' f autos (reqs, liveProof) = applySimps f (simps autos) (reqs, liveProof)

applySimps :: MonadFail m => ((String, Direction) -> MatchClass -> Bool) -> 
                             [(String, Direction)] -> (REqState, LiveProof) -> m LiveProof
applySimps f [] (reqs, liveProof) = fail ("No successful matching simp applys")
applySimps f (x:xs) (reqs, liveProof)
    = case matchFocusAgainst (fst x) liveProof of
        Yes liveProof' ->  case applyMatchToFocus1 1 liveProof' of
                                Nothing -> applySimps f xs (reqs, liveProof)
                                Just (mtch,fStdVars,gSubTerms,fLstVars,gLstVars)
                                  -> case f x (mClass mtch) of 
                                      False -> applySimps f xs (reqs, liveProof')
                                      True  -> case applyMatchToFocus2 vts mtch [] [] liveProof' of
                                                 Yes liveProof'' -> return liveProof''
                                                 But msgs        -> applySimps f xs (reqs, liveProof)
        But msgs       ->  applySimps f xs (reqs, liveProof)
   where
    vts = concat $ map thd3 $ mtchCtxts liveProof

applyFolds' :: MonadFail m => String -> AutoLaws -> (REqState, LiveProof) -> m LiveProof
applyFolds' input autos (reqs, liveProof) = do let match = if input == "f" then checkIsFold else checkIsUnFold
                                               let lws = if input == "f" then folds autos else unfolds autos
                                               applyFolds match lws (reqs, liveProof)

applyFolds :: MonadFail m => (MatchClass -> Bool) -> [String] -> (REqState, LiveProof) -> m LiveProof
applyFolds _ [] (reqs, liveProof) = fail ("No successful matching simp applys")
applyFolds f (x:xs) (reqs, liveProof)
    = case matchFocusAgainst x liveProof of
        Yes liveProof' ->  case applyMatchToFocus1 1 liveProof' of
                                Nothing -> applyFolds f xs (reqs, liveProof)
                                Just (mtch,fStdVars,gSubTerms,fLstVars,gLstVars)
                                  -> case f (mClass mtch) of 
                                      False -> applyFolds f xs (reqs, liveProof')
                                      True  -> case applyMatchToFocus2 vts mtch [] [] liveProof' of
                                                 Yes liveProof'' -> return liveProof''
                                                 But msgs        -> applyFolds f xs (reqs, liveProof)
        But msgs       ->  applyFolds f xs (reqs, liveProof)
   where
    vts = concat $ map thd3 $ mtchCtxts liveProof
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
  = case matchFocus ranking liveProof of
     Yes liveProof' ->  return (reqs, liveProof')
     But msgs
       -> do putStrLn $ unlines' msgs
             waitForReturn
             return (reqs, matches_ [] liveProof)
  where
    ranking = filterAndSort (matchFilter $ settings reqs, favourDefLHSOrd)

matchLawCommand args state@(reqs, liveProof)
  =  case matchFocusAgainst lawnm liveProof of
      Yes liveProof'  ->  return (reqs, liveProof')
      But msgs
       -> do putStrLn $ unlines' msgs
             waitForReturn
             return (reqs, matches_ [] liveProof)
  where
    lawnm = filter (not . isSpace) $ unwords args
\end{code}

Showing match details (dev-mode)
\begin{code}
showMatchesDescr = ( "shr"
                   , "show match replacements (uninstantiated)"
                   , unlines
                      [ "shr    -- show all replacements"
                      , "shr n -- show first n replacements."
                      , "--  uninstantiated: in 'law-space'."
                      ]
                   , showMatchesCommand )

showMatchesCommand :: REPLCmd (REqState, LiveProof)
showMatchesCommand args (reqs, liveProof)
  =  do putStrLn $ unlines' $ map (show . mRepl) moi
        waitForReturn
        return (reqs, liveProof)
  where
    n = args2int args
    mtchs = matches liveProof
    moi = if n > 0 then take n mtchs else mtchs
\end{code}

Showing proof settings:
\begin{code}
showProofSettingsDescr = ( "sps"
                         , "show proof settings"
                         , ""
                         , showPrfSettingsCommand )
showPrfSettingsCommand :: REPLCmd (REqState, LiveProof)
showPrfSettingsCommand _ pstate@(reqs, _)
  =  do putStrLn $ observeSettings reqs
        waitForReturn
        return pstate
\end{code}

Modifying proof settings:
\begin{code}
modPrfSettingsDescr
  = ( "mps"
    , "modify proof-settings"
    , unlines
        ( [ "mps 'setting' 'value' -- set setting=value" ]
          ++ map (("      "++) .showSettingStrings) rEqSettingStrings
          ++ ["  e.g. mps mmd 42"]
        )
    , modProofSettings )

modProofSettings :: REPLCmd (REqState, LiveProof)
modProofSettings args@[name,val] state@(reqs, liveProof)
-- | cmd == setSettings
    =  case modifySettings args reqs of
         But msgs  ->  do putStrLn $ unlines' ("mps failed":msgs)
                          waitForReturn
                          return (reqs, liveProof)
         Yes reqs' -> return (reqs', liveProof)
modProofSettings _ state = return state
\end{code}


Apply SAT-solver
\begin{code}

applySATDescr = ("sat"
              , "Apply SAT-solver"
              , ""
              , applySATCommand)

applySATCommand :: REPLCmd (REqState, LiveProof)
applySATCommand _ (reqs,liveproof)
  = case applySAT liveproof of
      Yes liveproof' -> return (reqs, liveproof')
      But msgs -> do putStrLn $ unlines' msgs
                     waitForReturn
                     return (reqs, liveproof) 
\end{code}

\newpage
Applying a match.
\begin{code}
applyMatchDescr = ( "a", "apply match"
                  , "a i  -- apply match number i", applyMatch )
\end{code}
We start by obtaining the match and information about floating variables
and possible matches (API Part 1).
We then let the user choose how to replace floating variables.
We then finish off the match application (API Part 2).
\begin{code}
applyMatch :: REPLCmd (REqState, LiveProof)
applyMatch args pstate@(reqs, liveProof)
  = case applyMatchToFocus1 (args2int args) liveProof of
      Nothing -> return pstate
      Just (mtch,fStdVars,gSubTerms,fLstVars,gLstVars)
       -> do let availTerms = theFalse : theTrue : gSubTerms
             (vardone,svtms)
               <-  fixFloatVars [] availTerms $ map StdVar fStdVars
             (lvardone,lvvls)
               <-  fixFloatLVars [] gLstVars $ map LstVar fLstVars
             if vardone && lvardone then
               case applyMatchToFocus2 vts mtch svtms lvvls liveProof of
                 Yes liveProof'
                  -> return(reqs, liveProof')
                 But msgs
                  -> do putStrLn $ unlines msgs
                        waitForReturn
                        return pstate
             else do putStrLn ( "Bad choices - done(var,lvar) = "
                             ++ show (vardone,lvardone) )
                     waitForReturn
                     return pstate
  where
    vts = concat $ map thd3 $ mtchCtxts liveProof
\end{code}
\newpage
Ask the user to specify a replacement term for each floating standard variable:
\begin{code}
    fixFloatVars :: [(Variable,Term)] -- replacements so far
                 -> [Term]            -- possible replacement terms
                 -> VarList           -- floating standard variables
                 -> IO (Bool,[(Variable,Term)])
    fixFloatVars vts _ []  = return (True,vts)
    fixFloatVars vts gterms@[term] ((StdVar v):stdvars)
      = do putStrLn ("-forced choice: "++trTerm 0 term)
           fixFloatVars ((v,term):vts) gterms stdvars
    fixFloatVars vts gterms ((StdVar v):stdvars)
      = do (chosen,term) <- pickThing ("Choose term to replace "++(trVar v))
                                     (trTerm 0) gterms
           if chosen
            then do putStrLn ("-chosen term is "++trTerm 0 term)
                    fixFloatVars ((v,term):vts) gterms stdvars
            else return (False,vts)
\end{code}
Ask the user to specify a replacement variable-list/set
for each floating list variable
(We currently assume that each replacement variable can only be associated
with one floating variable. Is this too restrictive?):
\begin{code}
    fixFloatLVars :: [(ListVar,VarList)] -- replacements so far
                  -> VarList             -- possible replacement variables
                  -> VarList             -- floating list-variables
                  -> IO (Bool,[(ListVar,VarList)])
    fixFloatLVars lvvls _ []        = return (True,lvvls)
    fixFloatLVars lvvls [] lstvars  = return (True,lvvls++empties)
      where
        fixAsEmpty (LstVar lvar) = (lvar,[])
        empties = map fixAsEmpty lstvars
    fixFloatLVars lvvls gvars ((LstVar lv):lstvars)
      = do (chosen,choices)
             <- takeThings ("Choose variables to replace "++(trLVar lv))
                           trGVar gvars
           if chosen
            then do let (wanted,leftover) = choices
                    putStrLn ("-chosen list is "++trVList wanted)
                    fixFloatLVars ((lv,wanted):lvvls) leftover lstvars
            else return (False,lvvls)
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
  = tryDelta (flattenAssociative $ theEqv) state
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
      Just gs -> tryDelta (groupAssociative theEqv gs) state
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
  = do let rslaws = lawInstantiate1 liveProof

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
                  let vts = concat $ map thd3 $ mtchCtxts liveProof
                  liveProof' <- lawInstantiate3 vts lawt vs2ts liveProof
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
  = tryDelta (cloneHypothesis (args2int args) theAnd) liveState
\end{code}

At any point in a proof, once at least one step has been taken,
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
\section{Development Commands}

\subsection{Builtin Theory Handling}

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

\subsection{In-Proof Test Commands}

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
  = do case tryFocusAgainst lawnm parts liveProof of
         Yes (bind,tPasC,scC',scP')
           -> putStrLn $ unlines
                [ banner
                , "Binding: " ++ trBinding bind
                -- , "Replacement: " ++ trTerm 0 repl
                -- , "Unbound: " ++ trVSet (findUnboundVars bind repl)
                , "Instantiated Law = " ++ trTerm 0 tPasC
                , "Instantiated Law S.C. = " ++ trSideCond scC'
                , "Goal S.C. = " ++ trSideCond (conjSC liveProof)
                , "Discharged Law S.C. = " ++ trSideCond scP']
         But msgs -> putStrLn $ unlines' ( (banner ++ " failed!") : msgs )
       userPause
       return state
  where
    (nums,rest) = span (all isDigit) args
    parts = map read nums
    lawnm = filter (not . isSpace) $ unwords rest
    banner = "Match against `"++lawnm++"'"++show parts
\end{code}


Test $\alpha$-equivalence of both sides of the sequent
\begin{code}
tryAlphaDescr = ( "ta"
                , "test LHS/RHS alpha-equivalence"
                , unlines
                   [ "ta             -- test LHS/RHS alphaequiv"
                   ]
                , tryAlpha)

tryAlpha :: REPLCmd (REqState, LiveProof)
tryAlpha _ state@( reqs, liveProof)
  = do case tryAlphaEquiv liveProof of
         Yes varmap
           -> putStrLn $ unlines
                [ banner
                , "Alpha-Equiv reports " ++ show varmap
                ]
         But msgs -> putStrLn $ unlines' ( (banner ++ " failed!") : msgs )
       userPause
       return state
  where
    banner = "Alpha Equivalence Check"
\end{code}
