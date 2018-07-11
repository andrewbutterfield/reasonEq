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
-- import TermZipper
-- import Laws
-- import Proofs
-- import Theories
-- import Sequents
-- import LiveProofs
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
       return $ ReqState thePropositionalLogic noTheories "" []

initState _
  = do putStrLn "Running in development mode."
       return $ ReqState thePropositionalLogic
                         testTheories
                         testName
                         []

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
reqCommands = [ cmdShow, cmdSet, cmdProve ]

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
        , "sh "++shLivePrf++" -- show current proof"
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
\subsection{Prove Command}
\begin{code}
cmdProve :: REqCmdDescr
cmdProve
  = ( "P"
    , "do a proof"
    , unlines
       [ "P i"
       , "i : conjecture number"
       , "no arg required if proof already live."
       ]
    , doProof )

doProof args reqs
  = case liveProofs reqs of
      []
       ->  do putStrLn "No current proof, will try to start one."
              case nlookup (getProofArgs args) (getCurrConj reqs) of
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
                         Just seq
                           -> proofREPL reqs (launchProof thylist nm asn seq)
      [prf]
       ->  do putStrLn "Back to (only) current proof."
              proofREPL reqs prf
      (prf:_) -- need to offer choice here
       ->  do putStrLn "Back to the (first of the ) current proofs."
              proofREPL reqs prf
  where
    getProofArgs [] = 0
    getProofArgs (a:_) = readInt a
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    currTh = currTheory reqs
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys
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
proofREPLprompt justHelped (_,proof)
  | justHelped  =  unlines' [ dispLiveProof proof
                            , "proof: "]
  | otherwise   =  unlines' [ clear -- clear screen, move to top-left
                            , dispLiveProof proof
                            , "proof: "]

proofEOFReplacement = []

proofREPLParser = charTypeParse

proofREPLQuitCmds = ["q"]

proofREPLQuit args (reqs,proof)
  = do putStr "Proof Incomplete, Abandon ? [Y] : "
       hFlush stdout
       inp <- getLine
       if inp == "Y"
        then return (True,( liveProofs_ []      reqs, proof))
        else return (True,( liveProofs_ [proof] reqs, proof))

proofREPLHelpCmds = ["?"]

proofREPLEndCondition (reqs,proof)
  =  proofComplete (logic reqs) proof

proofREPLEndTidy _ (reqs,proof)
  = do putStrLn "Proof Complete"
       let prf = finaliseProof proof
       putStrLn $ displayProof prf
       return ( liveProofs_ []
                $ theories__ (addTheoryProof (currTheory reqs) prf)  reqs
              , proof )
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
proofREPL reqs proof
 = do (reqs',_) <- runREPL
                       (clear++"Prover starting...")
                       proofREPLConfig
                       (reqs,proof)
      return reqs'
\end{code}

We have a common pattern: try to update the live proof.
Accept if it suceeds, otherwise no change
\begin{code}
tryDelta :: Monad m => (b -> Maybe b) -> (a,b) -> m (a,b)
tryDelta focus (reqs, liveProof)
  = case focus liveProof of
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
lawInstantiateProof _ (reqs, liveProof )
  | currt /= true
    = return (reqs, liveProof)
  | otherwise
    = do putStrLn $ showLaws rslaws
         putStr "Pick a law : " ; input <- getLine
         case input of
           str@(_:_) | all isDigit str
             -> case nlookup (read str) rslaws of
                 Just law@((nm,(lawt,_)),prov)
                   -> do putStrLn ("Law Chosen: "++nm++"  "++trTerm 0 lawt)
                         instantiateLaw reqs liveProof law
                 _ -> return (reqs, liveProof)
           _ -> return (reqs, liveProof)
  where
    currt = getTZ $ fst $ focus liveProof
    true = theTrue $ logic reqs
    thrys = fromJust $ getTheoryDeps (currTheory reqs) $ theories reqs
    rslaws = concat $ map laws thrys

instantiateLaw reqs liveProof law@((lnm,(lawt,lsc)),_)
 = let (tz,seq') = focus liveProof
       psc = conjSC liveProof
       dpath = fPath liveProof
   in
   do lbind <- generateLawInstanceBind (map known thrys)
                                       (exitTZ tz) psc law
      case instantiateSC lbind lsc of
        Nothing -> return (reqs, liveProof)
        Just ilsc
          -> do putStrLn $ trBinding lbind
                case mrgSideCond psc ilsc of
                  Nothing -> return (reqs, liveProof)
                  Just nsc ->
                    do  ilawt <- instantiate lbind lawt
                        return ( reqs
                               , focus_ (setTZ ilawt tz,seq')
                               $ stepsSoFar__
                                  ( ( (UseLaw ByInstantiation lnm lbind dpath)
                                    , exitTZ tz ) : )
                                  liveProof )
 where
    thrys = fromJust $ getTheoryDeps (currTheory reqs) $ theories reqs
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
      putStrLn "Goal sub-terms:"
      putStrLn $ numberList (trTerm 0) subGTerms           
      requestInstBindings emptyBinding subGTerms $ S.toList lFreeVars
\end{code}

\begin{code}
requestInstBindings bind gterms []  =  return bind
requestInstBindings bind gterms vs@(v:vrest)
 = do putStr ("Binding for "++trVar v++" ? ") ; input <- getLine
      case input of
       str@(_:_) | all isDigit str
         -> case nlookup (read str) $ gterms of
             Just gterm
               -> do bind' <- bindVarToTerm v gterm bind
                     requestInstBindings bind' gterms vrest
             _ -> requestInstBindings bind gterms vs
       _ -> requestInstBindings bind gterms vs
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
