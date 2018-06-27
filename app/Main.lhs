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
import RDAG
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
    , theories :: Theories
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
         $ ReqState thePropositionalLogic M.empty [] Nothing []

initState _
  = do putStrLn "Running in development mode."
       let reqs = ReqState thePropositionalLogic
                           propositionsAsTheories
                           (conjectures theoryPropositions)
                           Nothing []
       return reqs

propositionsAsTheories = fromJust $ addTheory theoryPropositions M.empty
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
reqCommands = [ cmdShow, cmdProve ]

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
        , "sh "++shConj++" -- show current conjectures"
        , "sh "++shLivePrf++" -- show current proof"
        , "sh "++shProofs++" -- show completed proofs"
        ]
    , showState )

shLogic = "="
shTheories = "t"
shConj = "c"
shLivePrf = "p"
shProofs = "P"

showState [cmd] reqs
 | cmd == shLogic     =  doshow reqs $ showLogic $ logic reqs
 | cmd == shTheories  =  doshow reqs $ showTheories $ theories reqs
 | cmd == shConj      =  doshow reqs $ showNmdAssns  $ conj reqs
 | cmd == shLivePrf   =  doshow reqs $ showLivePrf $ proof reqs
 | cmd == shProofs    =  doshow reqs $ showProofs $ proofs reqs
showState _ reqs      =  doshow reqs "unknown 'show' option."


doshow reqs str  =  putStrLn str >> return reqs
\end{code}

\newpage
\subsection{Prove Command}
\begin{code}
cmdProve :: REqCmdDescr
cmdProve
  = ( "prove"
    , "do a proof"
    , unlines
       [ "prove i"
       , "i : conjecture number"
       , "no arg required if proof already live."
       ]
    , doProof )


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
                         Nothing   -> doshow reqs "Invalid strategy no"
                         Just seq
                           -> proofREPL reqs (launchProof thylist nm asn seq)
      Just proof
       ->  do putStrLn "Back to current proof."
              proofREPL reqs proof
  where
    getProofArgs [] = 0
    getProofArgs (a:_) = readInt a
    thys = theories reqs
    -- hack! need to have notion of a 'current' theory.
    thylist = fromJust $ getTheoryDeps "PropLogic" thys
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
        then return (True,( proof_ Nothing      reqs, proof))
        else return (True,( proof_ (Just proof) reqs, proof))

proofREPLHelpCmds = ["?"]

proofREPLEndCondition (reqs,proof)
  =  proofComplete (logic reqs) proof

proofREPLEndTidy _ (reqs,proof)
  = do putStrLn "Proof Complete"
       let prf = finaliseProof proof
       putStrLn $ displayProof prf
       return ( proof_ Nothing $ proofs__ (prf:) reqs, proof)
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

args2int args = if null args then 0 else readInt $ head args
\end{code}

Focus movement commands
\begin{code}
goDownDescr = ( "d", "down", "d n  -- down n", goDown )


goDown :: REPLCmd (REqState, LiveProof)
goDown args (reqs,liveProof )
  = let i = args2int args
        (tz,seq') = focus liveProof
        (ok,tz') = downTZ i tz
    in if ok
        then return ( reqs
                    , focus_ (tz',seq')
                    $ fPath__ (++[i])
                    $ matches_ [] liveProof )
        else return (reqs, liveProof)

goUpDescr = ( "u", "up", "u  -- up", goUp )

goUp _ (reqs, liveProof )
  = let (tz,seq') = focus liveProof
        (ok,tz') = upTZ tz
    in if ok
        then return ( reqs
                    , focus_ (tz',seq')
                    $ fPath__ init
                    $ matches_ [] liveProof )
        else return (reqs, liveProof)
\end{code}

Switching consequent focus:
\begin{code}
switchConsequentDescr
  = ( "s", "switch",
      unlines' [ "s  -- switch between C_left/C_right"
               , "   -- or go to C_left if in hypothesis" ]
    , switchConsequent )

switchConsequent _ (reqs, liveProof)
  =  let
      sz = focus liveProof
      (ok,sw',sz') = switchLeftRight sz
     in if ok then return ( reqs
                          , focus_ sz'
                          $ matches_ []
                          $ stepsSoFar__
                             ((sw',exitTZ $ fst sz):) liveProof )
              else return ( reqs, liveProof )
\end{code}

Switching focus to a hypothesis:
\begin{code}
switchHypothesisDescr
  = ( "h", "to hypothesis"
    , "h i  -- focus on hypothesis i, use 'l' to exit."
    , switchHypothesis )

switchHypothesis args (reqs, liveProof)
  = let
      i = args2int args
      sz = focus liveProof
      (ok,sz') = seqGoHyp i sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok then return ( reqs
                         , mtchCtxts_ mcs
                         $ focus_ sz'
                         $ matches_ []
                         $ stepsSoFar__
                            ((SwHyp i, exitTZ $ fst sz):) liveProof )
             else return (reqs, liveProof)
\end{code}

Returning focus from a hypothesis:
\begin{code}
leaveHypothesisDescr
  = ( "l", "leave hypothesis"
    , "l  --  leave hypothesis, go to C_left."
    , leaveHypothesis )

leaveHypothesis _ (reqs, liveProof)
  = let
      sz = focus liveProof
      (ok,sz') = seqLeaveHyp sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if not ok
        then return ( reqs, liveProof )
        else return ( reqs
                         , mtchCtxts_ mcs
                         $ focus_ sz'
                         $ matches_ []
                         $ stepsSoFar__
                            ((SwLeft, exitTZ $ fst sz):) liveProof )
\end{code}

\newpage
Law Matching
\begin{code}
matchLawDescr = ( "m", "match laws", "m  -- match laws", matchLawCommand )

matchLawCommand _ (reqs, liveProof)
  = let (tz,_) = focus liveProof
        goalt = getTZ tz
    in do putStrLn ("Matching "++trTerm 0 goalt)
          let newMatches = matchInContexts (logic reqs)
                                           (mtchCtxts liveProof) goalt
          return (reqs, matches_ newMatches liveProof)

applyMatchDescr = ( "a", "apply match"
                  , "a i  -- apply match number i", applyMatch)

applyMatch args (reqs, liveProof)
  = let i = args2int args
        (tz,seq') = focus liveProof
        dpath = fPath liveProof
    in
    case nlookup i $ matches liveProof of
     Nothing -> do putStrLn ("No match numbered "++ show i)
                   return (reqs, liveProof)
     Just (MT lnm lasn bind repl)
      -> case instantiate bind repl of
          Nothing -> do putStrLn "Apply failed !"
                        return (reqs, liveProof)
          Just brepl
            -> do putStrLn ("Applied law '"++lnm++"' at "++show dpath)
                  return ( reqs
                         , focus_ ((setTZ brepl tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                               (((UseLaw ByMatch lnm bind dpath), exitTZ tz):)
                               liveProof )
\end{code}

\newpage
Law Instantiation.
Replacing \textit{true} by a law, with unknown variables
suitably instantiated.
\begin{code}
lawInstantiateDescr = ( "i", "instantiate"
                      , "i  -- instantiate a true focus with an law"
                      , lawInstantiateProof )
lawInstantiateProof _ (reqs, liveProof )
  | currt /= true
    = do putStrLn ("Can only instantiate an law over "++trTerm 0 true)
         return (reqs, liveProof)
  | otherwise
    = do putStrLn $ showLaws rslaws
         putStr "Pick a law : " ; input <- getLine
         case input of
           str@(_:_) | all isDigit str
             -> case nlookup (read str) rslaws of
                 Just law@((nm,asn),prov)
                   -> do putStrLn ("Law Chosen: "++nm)
                         instantiateLaw reqs liveProof law
                 _ -> return (reqs, liveProof)
           _ -> return (reqs, liveProof)
  where
    currt = getTZ $ fst $ focus liveProof
    true = theTrue $ logic reqs
    -- hack ! Need notion of 'current' theory
    thrys = fromJust $ getTheoryDeps "PropLogic" $ theories reqs
    rslaws = if null thrys then [] else laws (head thrys)

instantiateLaw reqs liveProof law@((lnm,(lawt,lsc)),_)
 = let (tz,seq') = focus liveProof
       psc = conjSC liveProof
       dpath = fPath liveProof
   in
   do lbind <- generateLawInstanceBind (map knownVars thrys)
                                       (exitTZ tz) psc law
      case instantiateSC lbind lsc of
        Nothing -> do putStrLn "instantiated law side-cond is false"
                      return (reqs, liveProof)
        Just ilsc
          -> do putStrLn $ trBinding lbind
                case mrgSideCond psc ilsc of
                  Nothing -> do putStrLn "side-condition merge failed"
                                return (reqs, liveProof)
                  Just nsc ->
                    do  ilawt <- instantiate lbind lawt
                        return ( reqs
                               , focus_ (setTZ ilawt tz,seq')
                               $ stepsSoFar__
                                  ( ( (UseLaw ByInstantiation lnm lbind dpath)
                                    , exitTZ tz ) : )
                                  liveProof )
 where
    -- hack ! Need notion of 'current' theory
    thrys = fromJust $ getTheoryDeps "PropLogic" $ theories reqs

\end{code}


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
Hypothesis Cloning, is based on the following law:
\[H \implies C \equiv H \implies H \land C\]
\begin{code}
cloneHypothesisDescr
  = ( "c", "clone hyp", "c i  -- clone hypothesis i"
    , cloneHypothesis )

cloneHypothesis args (reqs, liveProof)
  = let
      i = args2int args
      (tz,seq') = focus liveProof
      hypos = laws $ getHypotheses seq'
      currt = exitTZ tz
      land = theAnd $ logic reqs
    in case nlookup i hypos of
        Nothing -> return (reqs, liveProof)
        Just ((_,(hypt,_)),_)
          -> return
              ( reqs
              , focus_ (setTZ (PCons land [hypt,currt]) tz,seq')
              $ matches_ []
              $ stepsSoFar__
                 ( ( CloneH i
                   , exitTZ tz ) : )
                 liveProof )
\end{code}
