\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.Environment
import System.IO
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
import LexBase
import Variables
import AST
import VarData
import SideCond
import Binding
import REqState
import AbstractUI
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
\subsection{Initialising State}

At present, we assume development mode by default,
which currently initialises state based on the contents of
the hard-coded ``Propositional'' theory.
The normal ``user'' mode is not of much use right now.
\begin{code}
initState :: [String] -> IO REqState

initState ("user":_)
-- need to restore saved persistent state on startup
  = do putStrLn "Running in normal user mode."
       return $ ReqState thePropositionalLogic noTheories "" M.empty

initState _
  = do putStrLn "Running in development mode."
       return $ ReqState thePropositionalLogic
                         testTheories
                         (thName testTheory)
                         M.empty

testTheories
  =  fromJust $ addTheory testTheory $
     fromJust $ addTheory theoryPropositions noTheories

a = fromJust $ pVar $ Vbl (fromJust $ ident "A") PredV Static
b = fromJust $ pVar $ Vbl (fromJust $ ident "B") PredV Static
c = fromJust $ pVar $ Vbl (fromJust $ ident "C") PredV Static

cjHTest
 = ( "h-test"
   , ( a /\ (b /\ c) ==> (c /\ a) /\ (mkEquivs [b,b,b])
     , scTrue ) )

testName = "TestFortyTwo"

testTheory
  = Theory { thName  =  testName
           , thDeps  =  [ thName theoryPropositions ]
           , known   =  newVarTable
           , laws    =  []
           , proofs  =  []
           , pausedProofs = []
           , conjs   =  [ cjHTest ]
           }
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
reqCommands = [ cmdShow, cmdSet, cmdNewProof, cmdRet2Proof ]

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
repl :: [String] -> IO ()
repl args
  = do reqs0 <- initState args
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
        [ "sh "++shLogic++" -- show current logic"
        , "sh "++shTheories++" -- show theories"
        , "sh "++shCurrThry++" -- show 'current' theory"
        , "sh "++shConj++" -- show current conjectures"
        , "sh "++shLivePrf++" -- show current (live) proof"
        , "sh "++shProofs++" -- show completed proofs"
        ]
    , showState )

shLogic = "="
shTheories = "t"
shCurrThry = "T"
shConj = "c"
shLivePrf = "p"
shProofs = "P"

-- these are not robust enough - need to check if component is present.
showState [cmd] reqs
 | cmd == shLogic     =  doshow reqs $ observeLogic reqs
 | cmd == shTheories  =  doshow reqs $ observeTheories reqs
 | cmd == shCurrThry  =  doshow reqs $ observeCurrTheory reqs
 | cmd == shConj      =  doshow reqs $ observeCurrConj reqs
 | cmd == shLivePrf   =  doshow reqs $ observeLiveProofs reqs
 | cmd == shProofs    =  doshow reqs $ observeCompleteProofs reqs
showState _ reqs      =  doshow reqs "unknown 'show' option."

doshow reqs str  =  putStrLn str >> return reqs
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
       [ "N i"
       , "i : conjecture number"
       ]
    , doNewProof )

doNewProof args reqs
  = case nlookup (args2int args) (getCurrConj reqs) of
      Nothing  ->  do putStrLn "invalid conjecture number"
                      return reqs
      Just nconj@(nm,asn)
       -> do let strats
                  = availableStrategies (logic reqs)
                                        thys
                                        currTh
                                        nconj
             putStrLn $ numberList presentSeq $ strats
             putStr "Select sequent:- " ; choice <- getLine
             let six = readInt choice
             case nlookup six strats of
               Nothing   -> doshow reqs "Invalid strategy no"
               Just seqnt
                 -> proofREPL reqs (launchProof thylist currTh nm asn seqnt)
  where
    currTh = currTheory reqs
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys
\end{code}

\begin{code}
cmdRet2Proof :: REqCmdDescr
cmdRet2Proof
  = ( "r"
    , "return to live proof"
    , unlines
       [ "r i"
       , "i : optional live proof number"
       ]
    , doBack2Proof )

doBack2Proof args reqs
  = case M.elems $ liveProofs reqs of
      []        -> do putStrLn "No current live proofs."
                      return reqs
      [prf]     -> do putStrLn "Back to only live proof."
                      proofREPL reqs prf
      prfs      -> do let i = args2int args
                      if 1 <= i && i <= length prfs
                       then proofREPL reqs $ prfs!!(i-1)
                       else do putStrLn "No such live proof."
                               return reqs
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
        then return (True,( liveProofs__ del reqs, liveProof))
        else return (True,( liveProofs__ upd reqs, liveProof))
  where lpKey = (conjThName liveProof,conjName liveProof)
        del = M.delete lpKey
        upd = M.insert lpKey liveProof

proofREPLHelpCmds = ["?"]

proofREPLEndCondition (reqs,liveProof)
  =  proofComplete (logic reqs) liveProof

proofREPLEndTidy _ (reqs,liveProof)
  = do putStrLn "Proof Complete"
       let prf = finaliseProof liveProof
       putStrLn $ displayProof prf
       return ( liveProofs__ del
                $ theories__ (addTheoryProof currTh prf) reqs
              , liveProof )
  where lpKey = (conjThName liveProof,conjName liveProof)
        del = M.delete lpKey
        currTh = currTheory reqs
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
      ( map clearLong
            [ goDownDescr
            , goUpDescr
            , matchLawDescr
            , applyMatchDescr
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
  =  return (reqs, matchFocus (logic reqs) liveProof)
\end{code}

Applying a match.
\begin{code}
applyMatchDescr = ( "a", "apply match"
                  , "a i  -- apply match number i", applyMatch)

applyMatch :: REPLCmd (REqState, LiveProof)
applyMatch args  =  tryDelta (applyMatchToFocus (args2int args))
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
  = do let rslaws = lawInstantiate1 (logic reqs) liveProof

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
  = tryDelta (cloneHypothesis (args2int args) (theAnd $ logic reqs)) liveState
\end{code}
