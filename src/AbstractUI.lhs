\section{Abstract User-Interface}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module AbstractUI
( REqState
, observeSig, observeTheories, observeTheoryNames, observeLaws
, observeCurrTheory, observeCurrConj
, observeLiveProofs, observeCompleteProofs
, setCurrentTheory
, newProof1, newProof2, resumeProof
, abandonProof, saveProof, completeProof
, moveFocusDown, moveFocusUp, moveConsequentFocus
, moveFocusToHypothesis, moveFocusFromHypothesis
, matchFocus, applyMatchToFocus
, flattenAssociative, groupAssociative
, stepBack
, lawInstantiate1, lawInstantiate2, lawInstantiate3
, cloneHypothesis
, devBIRemind, devListAllBuiltins, devInstallBuiltin
)
where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.List

import Utilities
import LexBase
import Variables
import SideCond
import TermZipper
import AST
import Binding
import VarData
import Instantiate
import Sequents
import REqState
import Persistence

import TestRendering

import PropAxioms
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropMixOne
\end{code}

\subsection{Introduction}

We produce an abstract user-interface layer that wraps
around the proof-state as encapsulated in \texttt{REqState}.
The idea is that these functions are called by all concrete UIs,
either REPL-based or graphical.

There should be no direct link from a concrete UI to \texttt{REqState}.
For now this is a long-term goal.

We can break this abstract user-interface down into two main parts:
the first provides ways to observe the proof-state,
whilst the second supports modifications to that state.
Each of those parts will be further subdivided:
top-level (\texttt{REqState}),
and then lower level (.e.g., \texttt{LiveProofs}).

\subsection{Observing Proof-State (\texttt{REqState})}

The first issue to address here is in what form such observations
should be returned over an abstract interface,
remembering that the caller might be graphical, textual, or something else.
Possibilities range from returning text of some form,
through to actual data-structures.
However return, for example, a \texttt{Term},
requires the concrete UI to also have access to concrete ways to
handle and render terms.
This may not be an optimal `separation of concerns`.
Given that pretty-printing terms will be important, we may want
some form of structured text.
We also need to allow for the fact that the UI may use the observation structure
as a way to get user input for a subsequent modify operation.

In general we propose that observer functions will support
a number of return formats.

\subsubsection{Observing Current Logic}

\begin{code}
observeSig :: REqState -> String
observeSig reqs = showLogic $ logicsig reqs
\end{code}

\subsubsection{Observing Theories}

\begin{code}
observeTheories :: REqState -> String
observeTheories reqs = showTheories $ theories reqs

observeTheoryNames :: REqState -> String
observeTheoryNames
  = intercalate " ; " . map thName . getAllTheories . theories
\end{code}

\subsubsection{Observing Laws (and Conjectures)}

\begin{code}
observeLaws :: REqState -> String
observeLaws reqs
  = let thrys = getAllTheories $ theories reqs
    in hdr ++ (intercalate hdr $ map showTheoryLaws thrys)
  where hdr = "\n---\n"
\end{code}

\subsubsection{Observing Current Theory}

\begin{code}
observeCurrTheory :: REqState -> String
observeCurrTheory reqs
 = case getTheory (currTheory reqs) (theories reqs) of
     Nothing    ->  "No current theory."
     Just thry  ->  showTheoryLong thry
\end{code}

\subsubsection{Observing Current Conjectures}

\begin{code}
observeCurrConj :: REqState -> String
observeCurrConj reqs
  = case getTheory (currTheory reqs) (theories reqs) of
      Nothing    ->  "No current theory."
      Just thry  ->  showNmdAssns $ conjs thry
\end{code}

\subsubsection{Observing Live Proofs}

\begin{code}
observeLiveProofs :: REqState -> String
observeLiveProofs reqs = showLiveProofs $ liveProofs reqs
\end{code}


\subsubsection{Observing Completed Proofs}

\begin{code}
observeCompleteProofs :: REqState -> String
observeCompleteProofs reqs
  = case getTheory (currTheory reqs) (theories reqs) of
      Nothing    ->  "No current theory."
      Just thry  ->  showProofs $ proofs thry
\end{code}

\subsection{Modifying Proof-State (\texttt{REqState})}


\subsubsection{Setting Current Theory}

\begin{code}
setCurrentTheory :: Monad m => String -> REqState -> m REqState
setCurrentTheory thnm reqs
  = case getTheory thnm $ theories reqs of
      Nothing  ->  fail ("No theory named '"++thnm++"'.")
      Just _   ->  return ( currTheory_ thnm reqs)
\end{code}

\subsubsection{Adding a new conjecture}

\begin{code}
newConjecture :: Monad m => NmdAssertion -> REqState -> m REqState
newConjecture nasn@(nm,asn) reqs
  = fail "newConjecture NYI"
\end{code}

\subsubsection{Starting a Proof}

This is not a single abstract UI call,
but rather a series of calls, with all but the last
returning various items that need to be used by the concrete UI
to collect arguments for the next call.

\begin{code}
newProof1 :: Monad m => Int -> REqState
          -> m ( NmdAssertion
               , [(String,Sequent)] ) -- named strategy list
newProof1 i reqs
  = case nlookup i (getCurrConj reqs) of
      Nothing  ->  fail "invalid conjecture number"
      Just nconj -- @(nm,asn)
       -> return
           ( nconj
           , availableStrategies (logicsig reqs) thys currTh nconj )
  where
    currTh = currTheory reqs
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys

newProof2 :: Monad m => NmdAssertion -> [(String,Sequent)] -> Int -> REqState
          -> m LiveProof
newProof2 (nm,asn) strats six reqs
  = case nlookup six strats of
               Nothing   -> fail "Invalid strategy no"
               Just seqnt
                 -> return $ launchProof thylist currTh nm asn seqnt
  where
    currTh = currTheory reqs
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys
\end{code}

\subsubsection{Resuming a Proof}

\begin{code}
resumeProof :: Monad m => Int -> REqState -> m LiveProof
resumeProof i reqs
  = case M.elems $ liveProofs reqs of
      []     ->  fail "No current live proofs."
      [prf]  ->  return prf
      prfs   ->  if 1 <= i && i <= length prfs
                 then return $ prfs!!(i-1)
                 else fail "No such live proof."
\end{code}

\subsubsection{Abandoning a Proof}

\begin{code}
abandonProof :: REqState -> LiveProof -> REqState
abandonProof reqs liveProof
  = liveProofs__ del reqs
  where del = M.delete (conjThName liveProof,conjName liveProof)
\end{code}

\subsubsection{Saving a Proof}

\begin{code}
saveProof :: REqState -> LiveProof -> REqState
saveProof reqs liveProof
  = liveProofs__ upd reqs
  where upd = M.insert (conjThName liveProof,conjName liveProof) liveProof
\end{code}

\subsubsection{Completing a Proof}

\begin{code}
completeProof :: REqState -> LiveProof -> REqState
completeProof reqs liveProof
  = ( liveProofs__ del $ theories__ (upgrade . addProof) reqs )
  where prf = finaliseProof liveProof
        thnm = conjThName liveProof
        cjnm = conjName liveProof
        del = M.delete (thnm,cjnm)
        currTh = currTheory reqs -- should equal thnm !!!
        addProof = addTheoryProof currTh prf
        upgrade = upgradeConj2Law thnm cjnm
\end{code}

\subsection{Modifying Proof-State (\texttt{LiveProofs})}

\subsubsection{Moving Focus Down}

\begin{code}
moveFocusDown :: Monad m => Int -> LiveProof -> m LiveProof
moveFocusDown i liveProof
  = let (tz,seq') = focus liveProof
        (ok,tz') = downTZ i tz
    in if ok
        then return ( focus_ (tz',seq')
                    $ fPath__ (++[i])
                    $ matches_ [] liveProof )
        else fail ("No sub-term "++show i)

\end{code}

\subsubsection{Moving Focus Up}

\begin{code}
moveFocusUp :: Monad m => LiveProof -> m LiveProof
moveFocusUp liveProof
  = let (tz,seq') = focus liveProof
        (ok,tz') = upTZ tz
    in if ok
        then return ( focus_ (tz',seq')
                    $ fPath__ init
                    $ matches_ [] liveProof  )
        else fail "At top"

\end{code}

\subsubsection{Switching Consequent Focus}

\begin{code}
moveConsequentFocus :: Monad m => LiveProof -> m LiveProof
moveConsequentFocus liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = switchLeftRight sz
    in if ok
        then return ( focus_ sz'
                    $ matches_ []
                    $ stepsSoFar__ ((sw',exitTZ $ fst sz):) liveProof )
        else fail "Not in consequent"
\end{code}


\subsubsection{Focus into Hypotheses}

\begin{code}
moveFocusToHypothesis :: Monad m => Int -> LiveProof -> m LiveProof
moveFocusToHypothesis i liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = seqGoHyp i sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok
        then return ( mtchCtxts_ mcs
                    $ focus_ sz'
                    $ matches_ []
                    $ stepsSoFar__ ((sw', exitTZ $ fst sz):) liveProof )
        else fail ("No hypothesis "++show i)
\end{code}

\newpage
\subsubsection{Return Focus from Hypotheses}

\begin{code}
moveFocusFromHypothesis :: Monad m => LiveProof -> m LiveProof
moveFocusFromHypothesis liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = seqLeaveHyp sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok
        then return ( mtchCtxts_ mcs
                    $ focus_ sz'
                    $ matches_ []
                    $ stepsSoFar__ ((sw', exitTZ $ fst sz):) liveProof )
        else fail "Not in hypotheses"
\end{code}

\subsubsection{Match Laws against Focus}

\begin{code}
matchFocus :: LogicSig -> LiveProof -> LiveProof
matchFocus theSig liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        newMatches  =  matchInContexts theSig (mtchCtxts liveProof) goalt
    in matches_ newMatches liveProof
\end{code}

\subsubsection{Apply Match to Focus}

\begin{code}
applyMatchToFocus :: Monad m => Int -> LiveProof -> m LiveProof
applyMatchToFocus i liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
    in do mtch  <- nlookup i $ matches liveProof
          let bnd = mBind mtch
          brepl <- instantiate bnd (mRepl mtch)
          return ( focus_ ((setTZ brepl tz),seq')
                 $ matches_ []
                 $ stepsSoFar__
                    (((UseLaw ByMatch (mName mtch) bnd dpath), exitTZ tz):)
                    liveProof )
\end{code}


\subsubsection{Flattening and Grouping Associative Operators}

\begin{code}
flattenAssociative :: Monad m => Identifier -> LiveProof -> m LiveProof
flattenAssociative opI liveProof
  = let (tz,seq') = focus liveProof
        t = getTZ tz
    in case flattenAssoc opI t of
        But msgs -> fail $ unlines' msgs
        Yes t' -> return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__ (((Flatten opI,exitTZ tz)):)
                         $ liveProof )
\end{code}


\begin{code}
groupAssociative :: Monad m => Identifier -> GroupSpec -> LiveProof
                 -> m LiveProof
groupAssociative opI gs liveProof
  = let (tz,seq') = focus liveProof
        t = getTZ tz
    in case groupAssoc opI gs t of
        But msgs -> fail $ unlines' msgs
        Yes t' -> return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__ (((Associate opI gs,exitTZ tz)):)
                         $ liveProof )
\end{code}

\subsubsection{Stepping back a proof step.}

\begin{code}
stepBack  :: Monad m => Int -> LiveProof -> m LiveProof
stepBack i liveProof
  = return $ undoCalcStep liveProof
\end{code}

\newpage
\subsubsection{Law Instantiation}

Replacing \textit{true} by a law, with unknown variables
suitably instantiated.

This is not a single abstract UI call,
but rather a series of calls, with all but the last
returning various items that need to be used by the concrete UI
to collect arguments for the next call.

We start by checking that the focus is \true,
and that we can find some laws.
\begin{code}
lawInstantiate1 :: LogicSig -> LiveProof -> [Law]
lawInstantiate1 theSig liveProof
  = let currt = getTZ $ fst $ focus liveProof
        true = theTrue theSig
        rslaws = concat $ map fst $ mtchCtxts liveProof
    in if currt /= true then [] else rslaws
\end{code}

We should now get back those laws as well as the selected number.
We now get the law, and return it along with,
all the unknown free variables in the law,
and all the sub-terms of the complete proof goal.
\textbf{For now this is just the current top-level focus, i.e
one of the two consequents, or a hypothesis. For completeness
it should include both consequents, and  all the hypotheses
(This is a job for \texttt{Sequents}).}
\begin{code}
lawInstantiate2 :: Monad m
                => [Law] -> Int -> LiveProof -> m (Law,[Variable],[Term])
lawInstantiate2 rslaws i liveProof
  = do law@((lnm,(lawt,lsc)),lprov) <- nlookup i rslaws
       let (tz,seq') = focus liveProof
       let psc = conjSC liveProof
       let dpath = fPath liveProof
       let vts = concat $ map snd $ mtchCtxts liveProof
       let lFreeV = stdVarSetOf $ S.filter (isUnknownGVar vts) $ freeVars lawt
       let goalTerms = reverse $ subTerms (exitTZ tz)
       return (law,S.toList lFreeV,goalTerms)
\end{code}

We now get back a pairing of each law unknown free-variable
with one of the goal sub-terms, as well as the chosen law.
This gives us enough to complete the instantiation.
\begin{code}
lawInstantiate3 :: Monad m
                => Law -> [(Variable,Term)] -> LiveProof -> m LiveProof
lawInstantiate3 law@((lnm,(lawt,lsc)),lprov) varTerms liveProof
  = do lbind <- mkBinding emptyBinding varTerms
       ilsc <- instantiateSC lbind lsc
       nsc <- mrgSideCond (conjSC liveProof) ilsc
       ilawt <- instantiate lbind lawt
       let (tz,seq') = focus liveProof
       let dpath = fPath liveProof
       return ( focus_ (setTZ ilawt tz,seq')
                $ stepsSoFar__
                  ( ( (UseLaw ByInstantiation lnm lbind dpath), exitTZ tz ) : )
                  liveProof )

mkBinding bind [] = return bind
mkBinding bind ((v,t):rest)
  = do bind' <- bindVarToTerm v t bind
       mkBinding bind' rest
\end{code}

\newpage
\subsubsection{Clone Hypotheses}

\begin{code}
cloneHypothesis :: Monad m => Int -> Identifier -> LiveProof -> m LiveProof
cloneHypothesis i land liveProof
  = let
      (tz,seq') = focus liveProof
      hypos = laws $ getHypotheses seq'
      currt = exitTZ tz
    in case nlookup i hypos of
        Nothing -> fail ("No such hypothesis: "++show i)
        Just ((_,(hypt,_)),_)
          -> return ( focus_ (setTZ (PCons land [hypt,currt]) tz,seq')
                    $ matches_ []
                    $ stepsSoFar__ ( ( CloneH i, exitTZ tz ) : ) liveProof )
\end{code}

\newpage
\subsection{Development Features}

Listing builtin theories:
\begin{code}
devKnownBuiltins  = [ propAxiomTheory
                    , propEquivTheory
                    , propNotTheory
                    , propDisjTheory
                    , propConjTheory
                    , propMixOneTheory
                    ]

biLkp _ []  = Nothing
biLkp nm (th:ths)
 | nm == thName th  =  Just th
 | otherwise        =  biLkp nm ths

devListAllBuiltins :: String
devListAllBuiltins
  = summarise $ map thName devKnownBuiltins
  where
       summarise = intercalate " ; "
    -- summarise = unlines'

devBIRemind :: String
devBIRemind
  = "Remember to update AbstractUI.devKnownBuiltins with new builtins."
\end{code}

Installing builtin theories:
\begin{code}
devInstallBuiltin :: REqState -> String -> IO (Maybe String,REqState)
devInstallBuiltin reqs nm
  = case biLkp nm devKnownBuiltins of
      Nothing
        -> return ( Just ("devInstallBuiltin: no builtin theory '"++nm++"'")
                  , reqs)
      Just thry
        -> case addTheory thry $ theories reqs of
             But msgs -> return (Just $ unlines' msgs,reqs)
             Yes thrys' -> return (Nothing,reqs{theories=thrys'})
\end{code}
