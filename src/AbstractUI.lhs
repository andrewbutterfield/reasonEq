\section{Abstract User-Interface}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module AbstractUI
( REqState
, observeLogic, observeTheories, observeCurrTheory, observeCurrConj
, observeLiveProofs, observeCompleteProofs
, setCurrentTheory
, enterProof
, moveFocusDown, moveFocusUp, moveConsequentFocus
, moveFocusToHypothesis, moveFocusFromHypothesis
, matchFocus, applyMatchToFocus
, lawInstantiate1, lawInstantiate2, lawInstantiate3
, cloneHypothesis
)
where

import Data.Set (Set)
import qualified Data.Set as S

import Utilities
import LexBase
import Variables
import SideCond
import TermZipper
import AST
import Binding
import VarData
import Instantiate
import REqState
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
observeLogic :: REqState -> String
observeLogic reqs = showLogic $ logic reqs
\end{code}

\subsubsection{Observing Theories}

\begin{code}
observeTheories :: REqState -> String
observeTheories reqs = showTheories $ theories reqs
\end{code}

\subsubsection{Observing Current Theory}

\begin{code}
observeCurrTheory :: REqState -> String
observeCurrTheory reqs
 = case currTheory reqs of
     Nothing    ->  "No current theory."
     Just thry  ->  showTheoryLong thry
\end{code}

\subsubsection{Observing Current Conjectures}

\begin{code}
observeCurrConj :: REqState -> String
observeCurrConj reqs
  = case currTheory reqs of
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
  = case currTheory reqs of
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
      Just thry'
       ->  case currTheory reqs of
             Nothing  ->  return ( currTheory_ (Just thry') reqs)
             Just thry0
               ->  return ( currTheory_ (Just thry')
                          $ theories__ (replaceTheory thry0) reqs)
\end{code}

\subsubsection{Starting or Resuming a Proof}

\begin{code}
enterProof :: Monad m => REqState -> m REqState
enterProof reqs = return reqs

-- doProof args reqs
--   = case liveProofs reqs of
--       []
--        ->  do putStrLn "No current proof, will try to start one."
--               case nlookup (getProofArgs args) (getCurrConj reqs) of
--                 Nothing  ->  do putStrLn "invalid conjecture number"
--                                 return reqs
--                 Just nconj@(nm,asn)
--                  -> do let strats
--                             = availableStrategies (logic reqs)
--                                                   thys
--                                                   currTh
--                                                   nconj
--                        putStrLn $ numberList presentSeq $ strats
--                        putStr "Select sequent:- " ; choice <- getLine
--                        let six = readInt choice
--                        case nlookup six strats of
--                          Nothing   -> doshow reqs "Invalid strategy no"
--                          Just seq
--                            -> proofREPL reqs (launchProof thylist nm asn seq)
--       [prf]
--        ->  do putStrLn "Back to (only) current proof."
--               proofREPL reqs prf
--       (prf:_) -- need to offer choice here
--        ->  do putStrLn "Back to the (first of the ) current proofs."
--               proofREPL reqs prf
--   where
--     getProofArgs [] = 0
--     getProofArgs (a:_) = readInt a
--     getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
--     currTh = currTheory reqs
--     thys = theories reqs
--     thylist = fromJust $ getTheoryDeps currTh thys
--
-- presentSeq (str,seq)
--   = "'" ++ str ++ "':  "
--     ++ presentHyp (hyp seq)
--     ++ " " ++ _vdash ++ " " ++
--     trTerm 0 (cleft seq)
--     ++ " = " ++
--     trTerm 0 (cright seq)
--
-- presentHyp hthy
--   = intercalate "," $ map (trTerm 0 . fst . snd . fst) $ laws hthy
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
      (ok,sz') = seqGoHyp i sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok
        then return ( mtchCtxts_ mcs
                    $ focus_ sz'
                    $ matches_ []
                    $ stepsSoFar__ ((SwHyp i, exitTZ $ fst sz):) liveProof )
        else fail ("No hypothesis "++show i)
\end{code}

\newpage
\subsubsection{Return Focus from Hypotheses}

\begin{code}
moveFocusFromHypothesis :: Monad m => LiveProof -> m LiveProof
moveFocusFromHypothesis liveProof
  = let
      sz = focus liveProof
      (ok,sz') = seqLeaveHyp sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok
        then return ( mtchCtxts_ mcs
                    $ focus_ sz'
                    $ matches_ []
                    $ stepsSoFar__ ((SwLeft, exitTZ $ fst sz):) liveProof )
        else fail "Not in hypotheses"
\end{code}

\subsubsection{Match Laws against Focus}

\begin{code}
matchFocus :: TheLogic -> LiveProof -> LiveProof
matchFocus theLogic liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        newMatches  =  matchInContexts theLogic (mtchCtxts liveProof) goalt
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
lawInstantiate1 :: TheLogic -> LiveProof -> [Law]
lawInstantiate1 theLogic liveProof
  = let currt = getTZ $ fst $ focus liveProof
        true = theTrue theLogic
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
