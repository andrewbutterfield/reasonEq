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
import Data.Char

import NiceSymbols hiding (help)

import Utilities
import LexBase
import Variables
import AST
import VarData
import SideCond
import Binding
import TermZipper
import Proof
import Propositions
import Instantiate
import TestRendering
import REPL
\end{code}

\begin{code}
name = "reasonEq"
version = "0.5.2.0"
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
for every record field \texttt{fld :: rec -> t},
we define \texttt{fld\_\_ :: (t -> t) -> rec -> rec}
and derive \texttt{fld\_ :: t -> rec -> rec}.
\begin{verbatim}
fld__ f r = r{fld = f $ fld r} ;  fld_ = fld__ . const
\end{verbatim}
\begin{code}
data REqState
 = ReqState {
      logic :: TheLogic
    , theories :: [Theory]
    , conj :: [NmdAssertion]
    , proof :: Maybe LiveProof
    , proofs :: [Proof]
    }
logic__    f r = r{logic    = f $ logic r}   ; logic_    = logic__     . const
theories__ f r = r{theories = f $ theories r}; theories_ = theories__  . const
conj__     f r = r{conj     = f $ conj r}    ; conj_     = conj__      . const
proof__    f r = r{proof    = f $ proof r}   ; proof_    = proof__     . const
proofs__   f r = r{proofs   = f $ proofs r}  ; proofs_   = proofs__    . const
\end{code}

At present, we assume development mode by default,
which currently initialises state based on the contents of
the hard-coded ``Propositional'' theory.
The normal ``user'' mode is not of much use right now.
\begin{code}
initState :: [String] -> IO REqState

initState ("user":_)
-- need to restore saved persistent state on startup
  = do putStrLn "Running in normal user mode."
       return
         $ ReqState thePropositionalLogic [] [] Nothing []

initState _
  = do putStrLn "Running in development mode."
       let reqs = ReqState thePropositionalLogic
                           [theoryPropositions]
                           propConjs Nothing []
       return reqs
\end{code}

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
   minput <- getInputLine ("rEq."++_equiv++" ")
   case minput of
       Nothing      ->  quit reqs
       Just "quit"  ->  quit reqs
       Just input   ->  docommand reqs (words input) >>= loop

-- may ask for user confirmation, and save? stuff..
quit reqs = outputStrLn "Goodbye!"
-- need to save persistent state on exit
\end{code}

\subsubsection{REPL Command Repository types}
\begin{code}
type Command = [String] -> REqState -> InputT IO REqState
type CommDescr = ( String     -- command name
                 , String     -- short help for this command
                 , String     -- long help for this command
                 , Command )  -- command function
type Commands = [CommDescr]
\end{code}

\subsubsection{Command Respository Lookup}
\begin{code}
clookup :: String -> Commands -> Maybe CommDescr
clookup _ []  =  Nothing
clookup s (cd@(n,_,_,_):rest)
 | s == n     =  Just cd
 | otherwise  =  clookup s rest
\end{code}

\subsubsection{Command Repository}
\begin{code}
reqREPLcommands :: Commands
reqREPLcommands = [cmdShow,cmdSet,cmdProve]
\end{code}

\subsubsection{Command Dispatch}
\begin{code}
docommand :: REqState -> [String] -> InputT IO REqState
docommand reqs [] = return reqs
docommand reqs ("?":what)
 = help reqs what
docommand reqs (cmd:args)
 = case clookup cmd reqREPLcommands of
     Nothing -> outputStrLn ("unknown cmd: '"++cmd++"', '?' for help.")
                 >> return reqs
     Just (_,_,_,c)  ->  c args reqs
\end{code}

\subsubsection{Command Help}
\begin{code}
help reqs []
  = do outputStrLn "Commands:"
       outputStrLn "'?'     -- this help message"
       outputStrLn "'? cmd' -- help for 'cmd'"
       outputStrLn "Control-D or 'quit'  -- exit program."
       outputStrLn $ unlines $ map shorthelp reqREPLcommands
       return reqs
  where shorthelp (cmd,sh,_,_) = cmd ++ "  -- " ++ sh

help reqs (what:_)
  = case clookup what reqREPLcommands of
     Nothing -> outputStrLn ("unknown cmd: '"++what++"'") >> return reqs
     Just (_,_,lh,_) -> outputStrLn lh >> return reqs
\end{code}



\newpage
\subsection{Show Command }
\begin{code}
cmdShow :: CommDescr
cmdShow
  = ( "sh"
    , "show parts of the prover state"
    , unlines
        [ "sh "++shLogic++" - show current logic"
        , "sh "++shTheories++" - show theories"
        , "sh "++shConj++" - show current conjectures"
        , "sh "++shLivePrf++" - show current proof"
        , "sh "++shProofs++" - show completed proofs"
        ]
    , showState )

shLogic = "="
shTheories = "t"
shConj = "c"
shLivePrf = "p"
shProofs = "P"

showState [cmd] reqs
 | cmd == shLogic  =  doshow reqs $ showLogic $ logic reqs
 | cmd == shTheories  =  doshow reqs $ showTheories $ theories reqs
 | cmd == shConj   =  doshow reqs $ showNmdAssns  $ conj  reqs
 | cmd == shLivePrf  =  doshow reqs $ showLivePrf $ proof reqs
 | cmd == shProofs =  doshow reqs $ showProofs $ proofs reqs
showState _ reqs   =  doshow reqs "unknown 'show' option."

doshow reqs str   =  outputStrLn str >> return reqs

doshow' reqs str  =  putStrLn str    >> return reqs
\end{code}

\newpage
\subsection{Set Command}
\begin{code}
cmdSet
  = ( "set"
    , "set parts of prover state"
    , unlines
       [ "set not used right now"]
    , setState )

setState _ reqs = doshow reqs "unknown 'set' option"

-- list lookup by number [1..]
nlookup i things
 | i < 1 || null things  =  Nothing
nlookup 1 (thing:rest)   =  Just thing
nlookup i (thing:rest)   =  nlookup (i-1) rest

-- association list lookup
alookup name [] = Nothing
alookup name (thing@(n,_):rest)
  | name == n  =  Just thing
  | otherwise  =  alookup name rest
\end{code}

\newpage
\subsection{Prove Command}
\begin{code}
cmdProve
  = ( "prove"
    , "do a proof"
    , unlines
       [ "prove i"
       , "i : conjecture number"
       , "no arg required if proof already live."
       ]
    , \args reqs -> liftIO $ doProof args reqs)


doProof args reqs
  = case proof reqs of
      Nothing
       ->  do putStrLn "No current proof, will try to start one."
              case nlookup (getProofArgs args) (conj reqs) of
                Nothing  ->  do putStrLn "invalid conjecture number"
                                return reqs
                Just nconj@(nm,asn)
                 -> do let strats
                            = availableStrategies (logic reqs)
                                                  thys
                                                  nconj
                       putStrLn $ numberList presentSeq $ strats
                       putStr "Select sequent:- " ; choice <- getLine
                       let six = readInt choice
                       case nlookup six strats of
                         Nothing   -> doshow' reqs "Invalid strategy no"
                         Just seq
                           -> proofREPL reqs (launchProof thys nm asn seq)
      Just proof
       ->  do putStrLn "Back to current proof."
              proofREPL reqs proof
  where
    getProofArgs [] = 0
    getProofArgs (a:_) = readInt a
    thys = theories reqs
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
\subsubsection{Proof REPL}

We start by defining the proof REPL state:
\begin{code}
type ProofState
  = ( REqState   -- reasonEq state
    , LiveProof  -- current proof state
    , Bool )     -- true if last command was not 'help'
\end{code}
From this we can define most of the REPL configuration.
\begin{code}
proofREPLprompt (_,proof,nohelp)
  | nohelp    = unlines' [ "\ESC[2J\ESC[1;1H" -- clear screen, move to top-left
                         , dispLiveProof proof
                         , "proof: "]
  | otherwise = unlines' [ dispLiveProof proof
                         , "proof: "]

proofEOFReplacement = []

proofREPLParser = charTypeParse

proofREPLQuitCmds = ["q"]

proofREPLQuit args (reqs,proof,_)
  = do putStrLn "Proof Incomplete"
       putStr "Abandon ? [Y] : " ; inp <- getLine
       if inp == "Y"
        then return (True,( proof_ Nothing      reqs, proof, True))
        else return (True,( proof_ (Just proof) reqs, proof, True))

proofREPLHelpCmds = ["?"]

proofREPLEndCondition (reqs,proof,_)
  =  proofComplete (logic reqs) proof

proofREPLEndTidy _ (reqs,proof,_)
  = do putStrLn "Proof Complete"
       let prf = finaliseProof proof
       putStrLn $ displayProof prf
       return ( proof_ Nothing $ proofs__ (prf:) reqs, proof, True)
       -- Need to remove from conjectures and add to Laws
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
      []
      proofREPLEndCondition
      proofREPLEndTidy
\end{code}

This repl runs a proof.
\begin{code}
proofREPL reqs proof
 = do (reqs',_,_) <- runREPL
                       "Prover starting..."
                       proofREPLConfig
                       (reqs,proof,True)
      return reqs

-- proofREPL reqs proof
--  = do putStrLn ("\ESC[2J\ESC[1;1H") -- clear screen, move to top-left
--       proofREPL' reqs proof


proofREPL' reqs proof
 = do putStrLn $ dispLiveProof proof
      if proofComplete (logic reqs) proof
       then do putStrLn "Proof Complete"
               let prf = finaliseProof proof
               putStrLn $ displayProof prf
               return ( proof_ Nothing $ proofs__ (prf:) reqs)
       else
         do putStr "proof: " ; input <- getLine
            case input of
              "e" -> back reqs proof
              "?" -> proofHelp reqs proof
              pcmd -> proofCommand reqs proof (words pcmd)

back reqs proof
 = doshow' (proof_ (Just proof) reqs) "Back to main REPL, Proof still current."

proofHelp reqs proof
  = do putStrLn $ unlines
         [ "d n - down n"
         , "u - up"
         , "m - match laws"
         , "a n - apply match n"
         , "i - instantiate a true focus with an axiom"
         , "e - exit to top REPL, keeping proof"
         , "q - abandon proof"
         ]
       proofREPL' reqs proof

proofCommand reqs proof [('d':nstr)] = goDown reqs proof $ readInt nstr
proofCommand reqs proof ["d",nstr]   = goDown reqs proof $ readInt nstr
proofCommand reqs proof ["u"] = goUp reqs proof
proofCommand reqs proof ["m"] = matchLawCommand reqs proof
proofCommand reqs proof [('a':nstr)] = applyMatch reqs proof $ readInt nstr
proofCommand reqs proof ["a",nstr]   = applyMatch reqs proof $ readInt nstr
proofCommand reqs proof ["i"] = lawInstantiateProof reqs proof
proofCommand reqs proof ["q"] = abandonProof reqs proof
proofCommand reqs proof pcmds
  = do putStrLn ("proofCommand '"++unwords pcmds++"' unknown")
       proofREPL reqs proof
\end{code}

Focus movement commands
\begin{code}
goDown reqs proof@(nm, asn, sc, strat, mcs, (tz,seq'), dpath, _, steps ) i
  = let (ok,tz') = downTZ i tz in
    if ok
    then proofREPL reqs ( nm, asn, sc, strat
                        , mcs, (tz',seq'), dpath++[i], [], steps)
    else proofREPL reqs proof

goUp reqs proof@(nm, asn, sc, strat, mcs, (tz,seq'), dpath, _, steps )
  = let (ok,tz') = upTZ tz in
    if ok
    then proofREPL reqs ( nm, asn, sc, strat
                        , mcs, (tz',seq'), init dpath, [], steps)
    else proofREPL reqs proof
\end{code}

\newpage
Law Matching
\begin{code}
matchLawCommand reqs proof@(nm, asn, sc, strat, mcs, sz@(tz,_), dpath, _, steps)
  = do putStrLn ("Matching "++trTerm 0 goalt)
       let matches = matchInContexts (logic reqs) mcs goalt
       putStrLn $ displayMatches matches
       proofREPL reqs (nm, asn, sc, strat, mcs, sz, dpath, matches, steps)
  where goalt = getTZ tz

applyMatch reqs proof@(nm, asn, sc, strat, mcs, (tz,seq'), dpath, matches, steps) i
  = case alookup i matches of
     Nothing -> do putStrLn ("No match numbered "++ show i)
                   proofREPL reqs proof
     Just (_,(lnm,lasn,bind,repl))
      -> case instantiate bind repl of
          Nothing -> do putStrLn "Apply failed !"
                        proofREPL reqs proof
          Just brepl
            -> do putStrLn ("Applied law '"++lnm++"' at "++show dpath)
                  proofREPL reqs (nm, asn, sc, strat
                                 , mcs, ((setTZ brepl tz),seq')
                                 , dpath, []
                                 , (("match "++lnm,bind,dpath), exitTZ tz):steps)
\end{code}

Replacing \textit{true} by a law, with unknown variables
suitably instantiated.
\begin{code}
lawInstantiateProof reqs proof@( nm, asn, sc, strat
                               , mcs, sz@(tz,_), dpath, matches, steps)
  | currt /= true
    = do putStrLn ("Can only instantiate an law over "++trTerm 0 true)
         proofREPL reqs proof
  | otherwise
    = do putStrLn $ showLaws rslaws
         putStr "Pick a law : " ; input <- getLine
         case input of
           str@(_:_) | all isDigit str
             -> case nlookup (read str) rslaws of
                 Just law@((nm,asn),prov)
                   -> do putStrLn ("Law Chosen: "++nm)
                         instantiateLaw reqs proof law
                 _ -> proofREPL reqs proof
           _ -> proofREPL reqs proof
  where
    currt = getTZ tz; true = theTrue $ logic reqs
    thrys = theories reqs
    rslaws = if null thrys then [] else laws (head thrys)

instantiateLaw reqs proof@( pnm, asn, psc, strat
                          , mcs, (tz,seq'), dpath, matches, steps)
                    law@((lnm,(lawt,lsc)),_)
 = do lbind <- generateLawInstanceBind (map knownV $ theories reqs)
                                       (exitTZ tz) psc law
      case instantiateSC lbind lsc of
        Nothing -> do putStrLn "instantiated law side-cond is false"
                      proofREPL reqs proof
        Just ilsc
          -> do putStrLn $ trBinding lbind
                case mrgSideCond psc ilsc of
                  Nothing -> do putStrLn "side-condition merge failed"
                                proofREPL reqs proof
                  Just nsc ->
                    do  ilawt <- instantiate lbind lawt
                        proofREPL reqs ( pnm, asn, nsc, strat
                                       , mcs, (setTZ ilawt tz,seq')
                                       , dpath
                                       , matches
                                       , ( ("instantiate "++lnm,lbind,dpath)
                                           , exitTZ tz )
                                         : steps )
\end{code}

\newpage

Dialogue to get law instantiation binding.
We want a binding for every unknown variable in the law.
We display all such unknowns, and then ask for instantiations.
\begin{code}
generateLawInstanceBind vts gterm gsc law@((lnm,(lawt,lsc)),lprov)
 = do let lFreeVars = stdVarSetOf $ S.filter (isUnknownGVar vts)
                                  $ freeVars lawt
      putStrLn ("Free unknown law variables: "++trVariableSet lFreeVars)
      let subGTerms = reverse $ subTerms gterm
      -- let subGVars = map theVar $ filter isVar subGTerms
      requestInstBindings emptyBinding subGTerms $ S.toList lFreeVars
\end{code}

\begin{code}
requestInstBindings bind gterms []  =  return bind
requestInstBindings bind gterms vs@(v:vrest)
 = do putStrLn "Goal sub-terms:"
      putStrLn $ numberList (trTerm 0) gterms
      putStr ("Binding for "++trVar v++" ? ") ; input <- getLine
      case input of
       str@(_:_) | all isDigit str
         -> case nlookup (read str) $ gterms of
             Just gterm
               -> do bind' <- bindVarToTerm v gterm bind
                     requestInstBindings bind' gterms vrest
             _ -> requestInstBindings bind gterms vs
       _ -> requestInstBindings bind gterms vs
\end{code}

\newpage
Abandoning a proof, losing all work so far.
\begin{code}
abandonProof reqs proof
 = do putStr "Abandon ! Are you sure (Y/n) ? " ; yesno <- getLine
      case yesno of
        "Y" -> doshow' (proof_ Nothing reqs)
                      "Back to main REPL, Proof abandoned."
        _ -> proofREPL reqs proof
\end{code}
