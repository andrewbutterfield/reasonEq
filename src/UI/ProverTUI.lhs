\chapter{Prover TUI}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2017--25
              Saqid Zardari      2023
              Aaron Bruce        2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.ProverTUI where

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
import ProofSettings
import REqState
import MatchContext
import UI.AbstractUI
import Instantiate
import TestRendering
import SourceHandling
import UI.REPL
import Dev
import SAT
import Classifier
import ProofMatch

import Debugger
\end{code}

\newpage

\section{Proof REPL State}

We start by defining the proof REPL state:
\begin{code}
type ProofState
  = ( REqState   -- reasonEq state
    , LiveProof )  -- current proof state
\end{code}


From this we can define most of the REPL configuration.
\begin{code}
proofREPLdisplay justHelped ww (reqs,liveProof)
  | justHelped  =  unlines' disp
  | otherwise   =  unlines' ( clear -- clear screen, move to top-left
                              : disp )
  where
    disp = [ "WINDOW-WIDTH="++show ww, dispLiveProof liveProof ]

proofREPLprompt (reqs,liveProof) =  "proof:"

proofEOFReplacement = []

proofREPLParser = charTypeParse

proofREPLQuitCmds = ["q"]

proofREPLQuit args (reqs,liveProof)
  = do putStr "Proof Incomplete, Abandon ? [Y] : "
       hFlush stdout
       inp <- getLine
       if trim inp == "Y"
        then return (True,(abandonProof reqs liveProof, liveProof))
        else return (True,(updateProof reqs liveProof, liveProof))

proofREPLHelpCmds = ["?"]

proofREPLEndCondition (reqs,liveProof)
  =  proofIsComplete liveProof

proofREPLEndTidy _ (reqs,liveProof)
  = do putStrLn $ dispEndProof liveProof
       putStrLn "Proof Complete"
       return ( completeProof reqs liveProof, liveProof)
\end{code}

\newpage

The proof configuration
\begin{code}
proofREPLConfig
  = REPLC
      proofREPLdisplay
      proofREPLprompt
      proofEOFReplacement
      proofREPLParser
      proofREPLQuitCmds
      proofREPLQuit
      proofREPLHelpCmds
      ( map clearLong
            [ listScopeLawsDescr
            , listScopeTheoriesDescr
            , listScopeKnownsDescr
            , goDownDescr
            , goUpDescr
            , goBackDescr
            , matchLawDescr
            , applyMatchDescr
            -- , testDescr
            -- , normQuantDescr
            , simpNestDescr
            , substituteDescr
            , showProofSettingsDescr
            , modPrfSettingsDescr
            , saveLiveProofDescr
            , flatEquivDescr
            , groupEquivDescr
            , lawInstantiateDescr
            , applySATDescr
            , autoDescr
            , applyACLDescr
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
 = do (reqs',liveProof) 
       <- runREPL
                       (clear++"Prover starting...\n"++ observeSettings 
                       (liveSettings liveProof))
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

\section{Proof Settings}

Showing proof settings:
\begin{code}
showProofSettingsDescr = ( "sps"
                         , "show proof settings"
                         , "show proof settings"
                         , showPrfSettingsCommand )
showPrfSettingsCommand :: REPLCmd (REqState, LiveProof)
showPrfSettingsCommand _ pstate@(reqs, liveProof)
  =  do putStrLn $ observeSettings $ liveSettings liveProof
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
          ++ map (("      "++) .showPrfSettingStrings) prfSettingStrings
          ++ [ "Aliases for True: true t on yes y (any case), num > 0"
             , "Aliases for False: anything else"
             , "  e.g. mps tq on" ]
        )
    , modProofSettings )

modProofSettings :: REPLCmd (REqState, LiveProof)
modProofSettings args@[name,val] state@(reqs, liveProof)
-- | cmd == setSettings
    =  case modifyProofSettings args (liveSettings liveProof) of
         But msgs  ->  do putStrLn $ unlines' ("mps failed":msgs)
                          waitForReturn
                          return (reqs, liveProof)
         Yes prfset' -> do
           putStrLn $ observeSettings prfset'
           waitForReturn
           return (reqs, liveSettings_ prfset' liveProof)
modProofSettings _ state = return state
\end{code}

\section{Saving}

Saving the proof to a file:
\begin{code}
saveLiveProofDescr = ( "save"
                     , "save live-proof snapshot"
                     , ""
                     , saveLiveProofCommand )

saveLiveProofCommand :: REPLCmd (REqState, LiveProof)
saveLiveProofCommand _ pstate@(reqs, liveProof)
  =  do let reqs' = updateProof reqs liveProof
        reqs'' <- saveAllState reqs'
        putStrLn "Live proof saved"
        waitForReturn
        return (reqs'', liveProof)
\end{code}



\section{Listings}

Listing laws in scope for the current live proof.
\begin{code}
listScopeLawsDescr = ( "ll"
                     , "list laws"
                     , unlines
                        [ "ll -- list all laws in scope"
                        , "ll thnm1 ... thnmN -- in these theories only" ]
                     , listScopeLaws )

listScopeLaws :: REPLCmd (REqState, LiveProof)
listScopeLaws args state@( _, liveProof)
  = do putStrLn $ observeLawsInScope args liveProof
       userPause
       return state
\end{code}

Listing dependent theories for the current live proof.
\begin{code}
listScopeTheoriesDescr = ( "ld"
                         , "list dependencies"
                         , "ld -- list all dependent theories"
                         , listScopeTheories )

listScopeTheories :: REPLCmd (REqState, LiveProof)
listScopeTheories _ state@( reqs, liveProof)
  = do putStrLn $ observeTheoriesInScope liveProof
       userPause
       return state
\end{code}

Listing knowns in scope for the current live proof.
\begin{code}
listScopeKnownsDescr = ( "lk"
                       , "list knowns"
                       , "lk -- list all known names in scope"
                       , listScopeKnowns )

listScopeKnowns :: REPLCmd (REqState, LiveProof)
listScopeKnowns _ state@( reqs, liveProof)
  = do putStrLn $ observeKnownsInScope liveProof
       userPause
       return state
\end{code}

\section{Focus Management}

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
\section{Matching}

\subsection{Standard Law Matching}

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
    ranking = filterAndSort (matchFilter $ rdbn showPrfSettings "prfSttngs" $ liveSettings liveProof, favourDefLHSOrd)

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

\subsection{Show Match Replacements}

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

\newpage
\subsection{Applying a Match}

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
    vts = getVarTables $ mtchCtxts liveProof
\end{code}



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
      = do (chosen,term) 
             <- pickOrProvideThing 
                  ("Choose term to replace "++(trVar v))
                  (trTerm 0) (str2Term v) gterms
           if chosen
            then do putStrLn ("Chosen term is "++trTerm 0 term)
                    fixFloatVars ((v,term):vts) gterms stdvars
            else return (False,vts)

    str2Term v s 
      = case ident s of
          Yes i -> mkVarLike v i
          But msgs -> mkVarLike v $ jId "InvalidIdentifier"
      where
        mkVarLike v@(Vbl _ cls whn) i = jeVar $ Vbl i cls whn
\end{code}

\newpage

Ask the user to specify a replacement variable-list/set
for each floating list variable.
(We currently assume that each replacement variable can only be associated
with one floating variable. Is this too restrictive?  \textbf{Yes}):
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
             <- takeThings 
                 ("Choose variables (zero or more) to replace "++(trLVar lv))
                 trGVar gvars
           if chosen
            then do let (wanted,leftover) = choices
                    putStrLn ("Chosen list is "++trVList wanted)
                    fixFloatLVars ((lv,wanted):lvvls) leftover lstvars
            else return (False,lvvls)
\end{code}

\newpage
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
                   , "               --     we count from 1"
                   , "  -- n1..nk used in increasing order (sorted!)"
                   ]
                , tryMatch)

tryMatch :: REPLCmd (REqState, LiveProof)
tryMatch [] state = return state
tryMatch args state@( reqs, liveProof)
  = do  case tryFocusAgainst lawnm parts liveProof of
          Yes (bind,scP,tPasC,scC',scP') ->
            putStrLn $ unlines
              [ banner ++ " was successful"
              , "Binding:\n  " ++ trBinding bind
              , "Instantiated Replacement:\n  " ++ trTerm 0 tPasC
              , "Instantiated Variables: "  ++ trVSet (mentionedVars tPasC)
              , "Floating Vars?: " 
                ++ show (any isFloatingGVar $ mentionedVars tPasC)
              , "Law S.C.:\n  " ++ trSideCond scP 
              , "Instantiated Law S.C.:\n  " ++ trSideCond scC'
              , "Goal S.C.:\n  " ++ trSideCond (xpndSC liveProof)
              , "Discharged Law S.C.:\n  " ++ trSideCond scP']
          But msgs -> putStrLn $ unlines' ( (banner ++ " failed!") : msgs )
        userPause
        return state
  where
    (nums,rest) = span (all isDigit) args
    parts = sort $ filter (>0) $ map read nums
    lawnm = filter (not . isSpace) $ unwords rest
    banner = "Match against '"++lawnm++"'"++show parts
\end{code}

\newpage
\subsection{Checking Alpha-equivalence}


Test $\alpha$-equivalence of both sides of the sequent
\begin{code}
tryAlphaDescr = ( "ta"
                , "test LHS/RHS alpha-equivalence"
                , unlines
                   [ "ta     -- test LHS/RHS alphaequiv"
                   ]
                , tryAlpha)

tryAlpha :: REPLCmd (REqState, LiveProof)
tryAlpha _ state@( reqs, liveProof)
  = do  case tryAlphaEquiv liveProof of
          Yes varmap ->
            putStrLn $ unlines
              [ banner
              , "Alpha-Equiv reports " ++ show varmap
              ]
          But msgs -> 
            putStrLn $ unlines' ( (banner ++ " failed!") : msgs )
        userPause
        return state
  where
    banner = "Alpha Equivalence Check"
\end{code}


\section{High-Level Operations}

\subsection{Quantifier Handling}

% Normalise Quantifiers
% \begin{code}
% normQuantDescr = ( "nq"
%                  , "normalise quantifiers"
%                  , unlines
%                     [ "n       -- normalise quantifiers" ]
%                  , normQuantCommand )

% normQuantCommand :: REPLCmd (REqState, LiveProof)
% normQuantCommand _ state@(reqs, liveProof)
%   =  case normQuantFocus (theories reqs) liveProof of
%       Yes liveProof'  ->  return (reqs, liveProof')
%       But msgs
%        -> do putStrLn $ unlines' msgs
%              waitForReturn
%              return (reqs, matches_ [] liveProof)
% \end{code}


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
\subsection{Substitution Handling}


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

\subsection{Instantiation}

Law Instantiation.
Replacing \textit{true} by a law, with unknown variables
suitably instantiated.
\textbf{
Ideally this should replace the focus $F$ (any focus of type Bool)
by itself conjoined with the instantiation of any law $L$
($P(F)=P(F \land L[\lst e/\lst x])$)
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
                  let vts = getVarTables $ mtchCtxts liveProof
                  liveProof' <- lawInstantiate3 vts lawt vs2ts liveProof
                  return (reqs, liveProof' )
\end{code}

\newpage

\subsection{Hypothesis Handling}

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

\section{Automation}

\subsection{Equivalence Flattening}

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

\subsection{SAT-Solving}

Apply SAT-solver
\begin{code}
applySATDescr = ("sat"
              , "Apply SAT-solver"
              , "applies SAT-solver to focus"
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

\subsection{Auto Law Application}

Automatically apply laws of a specified kind
\begin{code}
autoDescr = ( "ala"
            , "automatic law application"
            , unlines
                [ "ala   -- apply simplification (default)"
                , "ala s -- apply simplification"
                , "ala c -- apply complexification"
                , "ala u -- unfold (expand) definition"
                , "ala f -- auto proof unfold"]
            , autoCommand )

autoCommand :: REPLCmd (REqState, LiveProof)
autoCommand args state@(reqs, liveProof)
  = case getTheory (currTheory reqs) $ theories reqs of
      Nothing ->
        do putStrLn ("Can't find current theory!!!\BEL")
           return (reqs, liveProof)
      Just thry ->
        do  let autos = allAutos thry $ theories reqs
            case whichApply input of
              True ->  
                case applyFolds' input autos (reqs, liveProof) of
                  Yes liveProof' -> return (reqs, liveProof')
                  But nothing -> 
                    do putStrLn ("No successful matching fold applies")
                       return (reqs, liveProof)
              False -> 
                do let isApplicable = if input == "c" 
                                      then checkIsComp else checkIsSimp
                   case applySimps' isApplicable autos (reqs, liveProof) of
                      Yes liveProof' -> return (reqs, liveProof')
                      But nothing -> 
                        do putStrLn ("No successful matching simp applies")
                           return (reqs, liveProof)
    where
      input = unwords args
\end{code}

\begin{code}
whichApply :: String -> Bool
whichApply "f" = True
whichApply "u" = True
whichApply _ = False

allAutos :: Theory -> TheoryDAG -> AutoLaws
allAutos thry thys 
  = do  let depthys = getTheoryDeps' (thName thry) thys
        combineAutos ((depAutos [] depthys) ++ [auto thry])

depAutos :: [AutoLaws] -> [Theory] -> [AutoLaws]
depAutos autos [] = autos
depAutos autos (depthy:depthys) = depAutos (autos ++ [auto depthy]) depthys
\end{code}

\newpage

Applying Simplifiers
\begin{code}
applySimps' :: MonadFail m 
            => ((String, Direction) -> MatchClass -> Bool) -> AutoLaws 
            -> (REqState, LiveProof) -> m LiveProof
applySimps' isApplicable autos (reqs, liveProof) 
  = applySimps isApplicable (simps autos) (reqs, liveProof)

applySimps :: MonadFail m 
           => ((String, Direction) -> MatchClass -> Bool) 
           -> [(String, Direction)] -> (REqState, LiveProof) -> m LiveProof
applySimps isApplicable [] (reqs, liveProof) 
  = fail ("No successful matching simp appliess")
applySimps isApplicable (x:xs) (reqs, liveProof)
  = case matchFocusAgainst (fst x) liveProof of
      Yes liveProof' ->  
        case applyMatchToFocus1 1 liveProof' of
          Nothing -> applySimps isApplicable xs (reqs, liveProof)
          Just (mtch,fStdVars,gSubTerms,fLstVars,gLstVars) ->
            case isApplicable x (mClass mtch) of 
              False -> applySimps isApplicable xs (reqs, liveProof')
              True  -> 
                case applyMatchToFocus2 vts mtch [] [] liveProof' of
                  Yes liveProof'' -> return liveProof''
                  But msgs -> applySimps isApplicable xs (reqs, liveProof)
      But msgs  ->  applySimps isApplicable xs (reqs, liveProof)
  where vts = getVarTables $ mtchCtxts liveProof
\end{code}

Applying Fold/Unfolds
\begin{code}
applyFolds' :: MonadFail m 
            => String -> AutoLaws -> (REqState, LiveProof) -> m LiveProof
applyFolds' input autos (reqs, liveProof) 
  = do  let isApplicable = if input == "f" then checkIsFold else checkIsUnFold
        let lws = folds autos 
        -- if input == "f" then folds autos else unfolds autos
        applyFolds isApplicable lws (reqs, liveProof)

applyFolds :: MonadFail m 
           => (MatchClass -> Bool) -> [String] 
           -> (REqState, LiveProof) -> m LiveProof
applyFolds _ [] (reqs, liveProof) 
  = fail ("No successful matching fold/unfold applies")
applyFolds isApplicable (x:xs) (reqs, liveProof)
  = case matchFocusAgainst x liveProof of
      Yes liveProof' ->  
        case applyMatchToFocus1 1 liveProof' of
          Nothing -> applyFolds isApplicable xs (reqs, liveProof)
          Just (mtch,fStdVars,gSubTerms,fLstVars,gLstVars) ->
            case isApplicable (mClass mtch) of 
              False -> applyFolds isApplicable xs (reqs, liveProof')
              True  -> 
                case applyMatchToFocus2 vts mtch [] [] liveProof' of
                  Yes liveProof'' -> return liveProof''
                  But msgs        -> applyFolds isApplicable xs (reqs, liveProof)
      But msgs       ->  applyFolds isApplicable xs (reqs, liveProof)
  where vts = getVarTables $ mtchCtxts liveProof
\end{code}

\newpage
\subsection{Classifier-Driven Automation (CDA)}

\begin{code}
acl = "automate classified laws"
applyACLDescr = ("acl"
                , acl
                , unlines'
                   [ "Invokes automatic application of classified laws"
                   , "to the focus and its sub-terms." ]
                , doClassDrivenAutomation)

doClassDrivenAutomation :: REPLCmd (REqState, LiveProof)
doClassDrivenAutomation _ (reqs,liveproof)
  = case applyCLA liveproof of
      Yes liveproof' -> return (reqs, liveproof')
      But msgs -> do putStrLn $ unlines' msgs
                     waitForReturn
                     return (reqs, liveproof) 
\end{code}




