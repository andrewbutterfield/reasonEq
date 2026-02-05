\chapter{Top-level TUI}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2017--25
              Saqid Zardari      2023
              Aaron Bruce        2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.TopTUI where

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

import ProgramIdentity
import LexBase
import Variables
import AST
import VarData
import Binding
import Typing
import SideCond
import Assertions
import Ranking
import ProofSettings
import REqState
import Instantiate
import TestRendering
import SourceHandling
import Dev
import SAT
import Classifier
import LiveProofs
import UI.AbstractTop
import UI.REPL
import UI.TSupport
import UI.ProverTUI

import Debugger
\end{code}


\newpage
\section{Top-Level REPL Definitions}

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
reqDisplay :: Bool -> Int -> REqState -> String
reqDisplay _ _ reqs = ""

reqPrompt :: REqState -> String
reqPrompt reqs = devMk ++ takeBaseName (projectDir reqs)++ "."
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
         saveAllState reqs
         byeBye
   byeBye = putStrLn "\nGoodbye!\n" >> return (True, reqs)

reqHelpCmds = ["?","help"]

reqCommands :: REqCommands
reqCommands = [ cmdShow, cmdSet, cmdNew
              , cmdNewProof, cmdRet2Proof
              , cmdLoad, cmdGenerate
              , cmdDump, cmdRestore
              , cmdGenerateConj, cmdLoadConj
              , cmdParseConj
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
  = REPLC reqDisplay reqPrompt reqEOFreplacmement reqParser
          reqQuitCmds reqQuit reqHelpCmds
          reqCommands
          reqEndCondition reqEndTidy
\end{code}

Running the REPL:
\begin{code}
tui :: REqState -> IO ()
tui reqs0
  = do runREPL reqWelcome reqConfig reqs0
       return ()

reqWelcome = unlines
 [ "Welcome to the "++progName++" "++progVersion++" TUI"
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
        , shName++" "++shLaws++" -- show laws in scope"
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
 | cmd == shSettings  =  doshow reqs $ observeSettings (prfSettings reqs)
showState _ reqs      =  doshow reqs "unknown/unimplemented 'show' option."

doshow :: REqState -> String -> IO REqState
doshow reqs str  =  putStrLn str >> return reqs

doCTshow :: REqState -> String -> String -> IO REqState
doCTshow reqs nm str = do
  theoryTxt <- showCurrentTheory nm reqs
  doshow reqs $ unlines' [ theoryTxt, str ]


showWorkspaces :: [String] -> REqState -> IO REqState
showWorkspaces args reqs
  = do (appFP,projects) <- getWorkspaces progName
       putStrLn ("Application Data:\n\t"++appFP)
       putStrLn ("Project Folders:\n"++unlines (map (('\t':) . thd3) projects))
       return reqs
\end{code}

\newpage
\section{State Save and Restore}

We process theories by default,
but can also handle smaller objects such as axioms, conjectures, and proofs.
\begin{code}
prfObj = "prf"
cnjObj = "cnj"
\end{code}

\textbf{We are introducing a simple text syntax for theories and related
artefacts, and we will ``generate'' to  and ``load'' from those.
These files will also be how we DEFINE theories, 
and will replace all/most(?) of the Haskell modules currently used
(the contents of \h{builtin/}).}
\begin{code}
genCmd  = "gen"  ; genSpc  = map (const ' ') genCmd
loadCmd = "load" ; loadSpc = map (const ' ') loadCmd
genLoadFormat
  = [ ( genSpc ++ " -- Theory source file: <thryname>-gen.utp" )
    , ( genSpc ++ " -- File format: plain text" ) ]
\end{code}

\begin{code}
cmdGenerate :: REqCmdDescr
cmdGenerate
  = ( genCmd
    , "generate theory source file"
    , unlines 
        ( (genCmd ++ " -- save current theory to source file")
        : genLoadFormat )
    , generateState )

generateState _ reqs = do
  let nm = currTheory reqs
  case getTheory nm $ theories reqs of
    Nothing    ->  generateState2 (thName_ nm nullTheory) reqs
    Just thry  ->  generateState2 thry reqs

generateState2 theory reqs = do
  let thnm = thName theory
  -- want to avoid overwriting existing .utp files
  let fname = projectDir reqs </> thnm </> (thnm++"-gen") <.> "utp"
  putStrLn("generating to "++fname)
  putStrLn ("saving "++fname)
  let theory_text = genTheory theory
  putStrLn ("Contents of "++fname++":\n"++theory_text)
  writeFile fname theory_text
  return reqs
\end{code}


\begin{code}
cmdLoad :: REqCmdDescr
cmdLoad
  = ( loadCmd
    , "loads theory from text file"
    , unlines
        ( (loadCmd ++ " <thry> -- load theory from <thry>.utp")
        : (loadSpc ++ "        -- warns if it modifies an existing theory" )
        : (loadSpc ++ "        -- creates a new theory if none exists" )
        : genLoadFormat )
    , loadTheoryFile )

loadTheoryFile [thName] reqs = do
  let fname = projectDir reqs </> thName </> thName <.> "utp" 
  putStrLn("loading from "++fname)
  haveSource <- doesFileExist fname
  if haveSource then do 
    theory_text <- readFile fname
    case loadTheory (theories reqs) theory_text of
      Yes pthry ->  do
        -- putStrLn ("Parsed as:\n"++show pthry)
        putStrLn ("Renders as:\n"++showTheoryLong (trTerm 0,trSideCond) pthry)
        putStrLn "\nComparing current and new theories\n"
        case getCurrentTheory reqs of
          Nothing -> putStrLn ("Can't find current theory: "++currTheory reqs)
          Just ithry -> do
            let report = compareIPTheories ithry pthry
            putStrLn report
        putStrLn "**** NOT YET INSTALLED ****"
      But msgs -> putStrLn $ unlines' ("theory parse failed":msgs)
  else putStrLn ("loadTheoryFile: cannot find "++fname)
  return reqs

loadTheoryFile args reqs = do
  putStrLn ("load: expected single theory name"); return reqs
\end{code}

\begin{code}
saveCmd = "save"
resCmd = "restore"
saveResWhat = "Prover artifacts: theories, proofs, conjectures, axioms."
saveRestoreFormat
  = [ " -- Theory source file: <thryname>.thr" 
    , " -- File format: sequences of Haskell datastructures" ]
\end{code}


\begin{code}
cmdDump :: REqCmdDescr
cmdDump
  = ( saveCmd
    , "save prover artefacts to file"
    , unlines
        [ ( saveCmd ++ "              -- save all prover" )
        , ( saveCmd ++ " .            -- save current theory" )
        , ( saveCmd ++ " <thry>       -- save theory <thry>" )
        , ( saveCmd ++ " "++prfObj++" <proof>  -- save proof <proof>" )
        , "To come:"
        , ( saveCmd ++ " cnj <conj>   -- save conjecture <cnj>" )
        , ( saveCmd ++ " ax <axiom>   -- save axiom <axiom>" )
        ]
    , saveState )

saveState [] reqs = saveAllState reqs
saveState [nm] reqs
  = let nm' = if nm == "." then (currTheory reqs) else nm
    in
    case getTheory nm' $ theories reqs of
      Nothing
       -> do putStrLn ("No such theory: '"++nm'++"'")
             return reqs
      Just thry
       -> do saveNamedTheory (projectDir reqs) (nm',thry)
             return reqs
saveState [what,nm] reqs
  | what == prfObj  = do
    let thnm = currTheory reqs 
    case ( getTheory thnm (theories reqs) 
            >>= find (pnm nm) . proofs
          ) of
      Nothing 
        ->  do  putStrLn ("No such proof: '"++nm++"'")
                return reqs
      Just prf 
        ->  do  saveProof (projectDir reqs) prf
                putStrLn ("Proof '"++nm++"' saved")
                return reqs
  where pnm nm (_,pn,_,_,_) = nm == pn
saveState _ reqs  =  doshow reqs "unknown 'save' option."
\end{code}

\newpage

\begin{code}
cmdRestore :: REqCmdDescr
cmdRestore
  = ( resCmd
    , "restore prover artefacts from file"
    , unlines

        [ ( resCmd ++ "             -- restore prover state" )
        , ( resCmd ++ " <thry>      -- restore theory <thry>" )
        , "   -- warns if it modifies an existing theory" 
        , ( resCmd ++ " " ++ prfObj 
                  ++ " <proof>      -- restore proof <proof>" )
        , "  CAUTION: will search for and restore into current theory (!)"
        , "To come:"
        , ( resCmd ++ " cnj <conj>  -- restore conjecture <cnj>" )
        , ( resCmd ++ " ax <axiom>  -- restore axiom <axiom>" )
        ]
    , restoreState )

restoreState [] reqs = do 
  let dirfp = projectDir reqs
  reqs' <- restoreAllState reqs dirfp
  return reqs'{ inDevMode = inDevMode reqs}
restoreState [nm] reqs = do
  let dirfp = projectDir reqs
  (ok,old,theories') <- restoreNamedTheory (theories reqs) dirfp nm
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
       
restoreState [what,nm] reqs | what == prfObj  = do
  let thnm = currTheory reqs
  let dirfp = projectDir reqs
  result <- restoreProof dirfp thnm nm
  case result of
    Nothing -> return reqs
    Just prf -> do 
      putStrLn ("Loading proof for "++nm)
      return $ theories__ (addTheoryProof thnm prf) reqs

restoreState _ reqs  =  doshow reqs "unknown 'restore' option."
\end{code}

\newpage
\section{Conjecture Management}


\subsection{Save Laws as Conjectures}

\begin{code}
cmdGenerateConj :: REqCmdDescr
cmdGenerateConj
  = ( "svc"
    , "save conjectures"
    , unlines
        [ "svc -- save all laws in current theory as conjectures"
        , "    -- saved to <currthry>/Conjectures.cnj"
        ]
    , saveAsConjectures )

saveAsConjectures _ reqs
  = case getTheory (currTheory reqs) $ theories reqs of
      Nothing
       -> do putStrLn ("Can't find current theory!!!\BEL")
             return reqs
      Just thry
       -> do let lawConjs = map lawNamedAssn (laws thry)
             let allConjs = lawConjs ++ conjs thry
             saveConjectures (projectDir reqs) (thName thry) allConjs
             return reqs
\end{code}

\subsection{Restore Conjectures}

\textbf{Just displays them for now}

\begin{code}
cmdLoadConj :: REqCmdDescr
cmdLoadConj
  = ( "resc"
    , "restore conjectures"
    , unlines
        [ "resc      -- display conjectures in current theory"
        , "resc <nm> -- display conjectures in <nm>/Conjectures.cnj "
        ]
    , displayConjectures )

displayConjectures [] reqs
  = do savedConjs <- restoreConjectures (projectDir reqs) (currTheory reqs)
       putStrLn $ unlines' $ map (trNmdAsn) savedConjs
       return reqs
displayConjectures [nm] reqs
  = do savedConjs <- restoreConjectures (projectDir reqs) nm
       putStrLn $ unlines' $ map (trNmdAsn) savedConjs
       return reqs
displayConjectures _ reqs  =  doshow reqs "unknown 'resc' option."
\end{code}

\newpage
\subsection{Parse Conjectures}

Pull conjectures in from a text file using a simple (clunky) syntax


\begin{code}
cmdParseConj :: REqCmdDescr
cmdParseConj
  = ( "prs"
    , "parse stuff"
    , unlines 
        [ "prs "++cnjObj++" conjname - parse conjecture from file" 
        , "    conjecture in <projdir>/<thnm>/<conjname>-conj.txt"
        , "   Probably obsolete"
        ]
    , parseEntities )

conjtxt = "-conj.txt"

parseEntities [cnj,cname] reqs
  | cnj == cnjObj = do
    thry <- getCurrentTheory reqs
    let projpath = projectDir reqs </> thName thry </> (cname++conjtxt)
    putStrLn ("Load conjecture from "++projpath)
    fileExists <- doesFileExist projpath
    if fileExists
    then do
      text <- readFile projpath
      putStrLn text
      case readConjecture text reqs of
        Yes reqs' ->  doshow reqs' "Parsed successfully"
        But msgs  -> doshow reqs $ unlines msgs
    else doshow reqs "File not found"
parseEntities _ reqs = doshow reqs "unknown parse option"
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
  =  case classifyLaw thname lwnm reqs of
         But lns     ->  doshow reqs  (unlines' lns)
         Yes reqs'
          | lwnm == "."  ->  doCTshow reqs' thname msg
          | otherwise    ->  doshow   reqs'        msg
 where 
   thname = currTheory reqs
   lwnm = args2str args
   msg = "Classify "++lwnm

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
          ++ map (("      "++) .showPrfSettingStrings) prfSettingStrings
          ++ ["  e.g. set X mmd 42"]
        )
    , setState )

setCurrThry = shCurrThry
setSettings = shSettings

setState (cmd:rest) reqs
 | cmd == setCurrThry
    =  case setCurrentTheory nm reqs of
         But msgs   ->  doshow reqs $ unlines' msgs
         Yes reqs'  ->  doCTshow reqs' nm 
                                 ("Current Theory now '" ++ nm ++ "'")
 | cmd == setSettings
    =  case modifyProofSettings rest (prfSettings reqs) of
         But msgs     ->  doshow reqs $ unlines' msgs
         Yes prfset'  ->  doshow (prfSettings_ prfset' reqs) 
                                ("Settings updated")
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
          , "new "++shConj++" 'conj_name' -- new conjecture 'conj_name'"
          ] ++ term_syntax )
    , newThing )

newThing cmdargs@[cmd,nm,fp] reqs
 | cmd == shWork = newWorkspace nm fp reqs
newThing (cmd:cnm:_) reqs
 | cmd == shConj = newConj cnm reqs
newThing _ reqs  =  doshow reqs "unknown 'new' option."
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
newConj cjnm reqs
  = do  let prompt = unlines term_syntax 
                     ++ "New conj, '"++cjnm++"', enter term :- "
        let preview = trTerm 0
        (ok,term) <- getConfirmedObject prompt parse preview
        if ok
          then 
            do  let asn' = mkAsn term scTrue
                case newConjecture 
                      (currTheory reqs) (cjnm,asn') reqs of
                  But msgs  -> doshow reqs (unlines' msgs)
                  Yes reqs' -> 
                    do putStrLn ("Conjecture '"++cjnm++"' installed")
                       return reqs'
          else return reqs

  where
    parse txt = But ["loadTerm needs upgrsading to new LBNF syntax"]
      --case loadTerm txt of
      --  But msgs         ->  But msgs
      --  Yes (term,[])    ->  Yes term
      --  Yes (term,xtra)  ->  But [ "Error: leftover tokens" 
      --                           , concat (map renderNNToken' xtra) ]
\end{code}
                  

\newpage
\section{Faking It}

Simply assuming conjectures as laws:
\begin{code}
cmdAssume :: REqCmdDescr
cmdAssume
  = ( "Assume"
    , "assume conjecture as law"
    , unlines
       [ "Assume name - assume conjecture 'name'"
       , "Assume lo hi - assume conjectures numbered lo,..,hi (incl.)"
       , "Assume . - assume all current theory conjectures"
       , "Assume * - assume all dependency theory conjectures"
       ]
    , doAssumption )

doAssumption args reqs
  =  case assumeConjecture thname args reqs of
         But lns     ->  doshow reqs  (unlines' lns)
         Yes reqs'
           | which == "."  ->  doCTshow reqs' thname msg
           | otherwise     ->  doshow   reqs'        msg
  where
   thname = currTheory reqs
   which = args2str args
   msg = "Assumed " ++ which
\end{code}


doshow reqs' 
                 ( (showTheoryLong (trTerm 0, trSideCond) thry')
                   ++ "Current Theory now '" ++ nm ++ "'" )

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
  =  case demoteLaw thname lwnm reqs of
         But lns     ->  doshow reqs  (unlines' lns)
         Yes reqs'   ->  doCTshow reqs' thname msg 
 where
   thname = currTheory reqs 
   lwnm = args2str args
   msg = "Demoted " ++ lwnm
\end{code}


\newpage
\section{Proof Access Commands}

\subsection{New Proof} 

\begin{code}
cmdNewProof :: REqCmdDescr
cmdNewProof
  = ( "N"
    , "new proof"
    , unlines
       [ "N - start new proof for a conjecture in current theory"       , "i : conjecture number"
       ]
    , doNewProof )

doNewProof _ reqs = do
  putStrLn "Starting new proof:"
  let currTh = currTheory reqs
  let thys = theories reqs
  let conjs = fromJust $ getTheoryConjectures currTh thys
  mconj <- selectByNumber fst conjs 
  case mconj of 
    But msgs -> errorPause msgs reqs
    Yes nconj -> do
      case newProof1 nconj reqs of
        But msgs -> errorPause msgs reqs
        Yes (nconj,strats) -> do 
          putStrLn "got strategy-list"
          mstrat <- selectByNumber presentSeq strats
          case mstrat of
            But msgs -> errorPause msgs reqs
            Yes seqnt -> do
              putStrLn "got sequent"
              case newProof2 nconj seqnt reqs of
                But msgs -> errorPause msgs reqs
                Yes liveProof -> proofREPL reqs liveProof
-- !!! there must be a way to listify the above!
\end{code}


\newpage
\subsection{Return to Live Proof}

\begin{code}
cmdRet2Proof :: REqCmdDescr
cmdRet2Proof
  = ( "r"
    , "return to live proof"
    , unlines
       [ "r  - return to a live proof."
       ]
    , doBack2Proof )

doBack2Proof _ reqs = do
  let lps = M.assocs $ liveProofs reqs
  mlp <- selectByNumber (show . fst) lps
  case mlp of
    Just (_,liveProof) -> proofREPL reqs liveProof
    Nothing ->  return reqs
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
    hstring  = intercalate "," 
               $ map (trTerm 0 . assnT . snd . fst) 
               $ laws hthy

strdir str
  | str == reduceBoth  =  "  --> ? <--  "
  | otherwise          =  "     -->     "
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
        , "    -- fails if theory already installed"
        , "b "++binReset++" <name> -- reset builtin theory <name>"
        , "    -- replaces already installed theory by builtin version"
        , "                               (a.k.a. 'factory setting')"
        , "b "++binUpdate++" <name> -- update builtin theory <name>"
        , "    -- adds in new material from builtin version"
        , "    -- asks user regarding revisions to existing material"
        , "b "++binUForce++" <name> -- force-update builtin theory <name>"
        , "    -- adds in new and revised material from builtin version"
        , "    -- does not ask user to confirm revisions"
        ]
    , buildIn )

binExists = "e" ; binInstalled = "i" ; binInstall = "I"
binReset = "R" ; binUpdate = "U" ; binUForce = "F"

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
