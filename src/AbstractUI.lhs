section{Abstract User-Interface}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--2021

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module AbstractUI
( REqState
, observeSig, observeTheories, observeTheoryNames, observeLaws
, observeKnowns
, observeCurrTheory, observeCurrConj
, observeLiveProofs, observeCompleteProofs
, setCurrentTheory
, newConjecture
, assumeConjecture, demoteLaw
, newProof1, newProof2, resumeProof
, abandonProof, saveProof, completeProof
, moveFocusDown
, moveDownNTimes, moveToBottom, followPath, mUGAM, numOfSubTerms, listOfSubTerms, checkSubTermsNumbers, listOfSubTermsNumbers, trySimplifyRecursively
, moveFocusUp, moveConsequentFocus
, moveFocusToHypothesis, moveFocusFromHypothesis
, matchFocus, matchFocusAgainst
, applyMatchToFocus1, applyMatchToFocus2
, normQuantFocus
, nestSimpFocus
, substituteFocus, revSubstituteFocus
, tryFocusAgainst
, observeLawsInScope, observeKnownsInScope
, flattenAssociative, groupAssociative
, stepBack
, lawInstantiate1, lawInstantiate2, lawInstantiate3
, cloneHypothesis
, stepEquivalenceTheorem
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
import Assertions
import TermZipper
import AST
import FreeVars
import Substitution
import Binding
import VarData
import Instantiate
import Sequents
import REqState
import Persistence
import Ranking

import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\subsection{Simplification Laws}
This is a list of the simplification laws that I will be using
\begin{code}

simplificationTheories :: [String]
simplificationTheories = ["Equiv","Not","Or","And","AndOrInvert"]

simplificationLaws :: String -> [String]
simplificationLaws "Equiv"  = ["true", "equiv_refl","equiv_id","equiv_symm","equiv_assoc"]
simplificationLaws "Not"  = ["lnot_invol","false_def", "false_neg", "lnot_equiv_distr"]
simplificationLaws "Or"  = ["lor_idem","excl-middle","lor_zero","lor_unit","lor_symm"]
simplificationLaws "And"  = ["land_idem", "land_unit", "contradiction"]
simplificationLaws "AndOrInvert" = ["land_lor_absorb","lor_land_absorb"]
simplificationLaws _ = []
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
observeLaws :: REqState -> [String] -> String
observeLaws reqs ["-u"]
  = let thrys = getAllTheories $ theories reqs
    in hdr ++ (intercalate hdr $ map (showTheoryLaws ud) $ reverse thrys)
  where hdr = "\n---\n"
        ud = (trTermU 0, trSideCondU)
observeLaws reqs _
  = let thrys = getAllTheories $ theories reqs
    in hdr ++ (intercalate hdr $ map (showTheoryLaws nd) $ reverse thrys)
  where hdr = "\n---\n"
        nd = (trTerm 0, trSideCond)
\end{code}

\subsubsection{Observing Known Names}

\begin{code}
observeKnowns :: REqState -> [String] -> String
observeKnowns reqs _
  = let thrys = getTheoryDeps' (currTheory reqs) $ theories reqs
    in hdr ++ (intercalate hdr $ map showTheoryKnowns thrys)
  where hdr = "\n---\n"
\end{code}

\subsubsection{Observing Current Theory}

\begin{code}
observeCurrTheory :: REqState -> String
observeCurrTheory reqs
 = case getTheory (currTheory reqs) (theories reqs) of
     Nothing    ->  "No current theory."
     Just thry  ->  showTheoryLong (trTerm 0, trSideCond) thry
\end{code}

\subsubsection{Observing Current Conjectures}

\begin{code}
observeCurrConj :: REqState -> [String] -> String
observeCurrConj reqs ["-u"]
  = case getTheory (currTheory reqs) (theories reqs) of
      Nothing    ->  "No current theory."
      Just thry  ->  showNmdAssns (trTermU 0, trSideCondU) $ conjs thry
observeCurrConj reqs _
  = case getTheory (currTheory reqs) (theories reqs) of
      Nothing    ->  "No current theory."
      Just thry  ->  showNmdAssns (trTerm 0, trSideCond) $ conjs thry
\end{code}

\subsubsection{Observing Live Proofs}

\begin{code}
observeLiveProofs :: REqState -> String
observeLiveProofs reqs = showLiveProofs $ liveProofs reqs
\end{code}


\subsubsection{Observing Completed Proofs}

\begin{code}
observeCompleteProofs :: [String] -> REqState -> String
observeCompleteProofs args reqs
  = case getTheory (currTheory reqs) (theories reqs) of
      Nothing    ->  "No current theory."
      Just thry  ->  showProofs args $ proofs thry
\end{code}

\subsection{Modifying Proof-State (\texttt{REqState})}


\subsubsection{Setting Current Theory}

\begin{code}
setCurrentTheory :: Monad m => String -> REqState -> m REqState
setCurrentTheory thnm reqs
  = case getTheory thnm $ theories reqs of
      Nothing  ->  fail ("No theory named '"++thnm++"'.")
      Just _   ->  return ( changed $ currTheory_ thnm reqs)
\end{code}

\subsubsection{Adding a new conjecture}

Easy, so long as we check for name clashes.
\begin{code}
newConjecture :: Monad m => String -> NmdAssertion -> REqState
              -> m REqState
newConjecture thnm nasn reqs
  = case getTheory thnm $ theories reqs of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry -> do thry' <- newTheoryConj nasn thry
                      return $ changed
                             $ theories__ (replaceTheory' thry') $ reqs
\end{code}

\subsubsection{Assuming Conjectures}

\begin{code}
assumeConjecture :: Monad m => String -> String -> REqState -> m REqState
assumeConjecture thnm whichC reqs
  = case getTheory thnm $ theories reqs of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry -> do thry' <- assumeConj whichC thry
                      return $ changed
                             $ theories__ (replaceTheory' thry') $ reqs
\end{code}

\subsubsection{Demoting Laws}

\begin{code}
demoteLaw :: Monad m => String -> String -> REqState -> m REqState
demoteLaw thnm whichL reqs
  = case getTheory thnm $ theories reqs of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry -> do thry' <- lawDemote whichL thry
                      return $ changed
                             $ theories__ (replaceTheory' thry') $ reqs
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
      Just nconj@(nm,asn)
        | shadowFree asn
            -> return
                ( nconj
                , availableStrategies (logicsig reqs) thys currTh nconj )
        | otherwise -> fail "shadowed bound-vars. in conjecture"
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

\newpage
\subsection{Removing Bound Variable ``Shadowing''}

We need to ensure that all bound variables in a conjecture
are not ``shadowed'' by bound variables nested deeper in,
as this makes matching and proofs-steps
much easier to implement.
For example, in
\[\forall x \bullet ( \dots (\exists x \bullet P) \dots)\]
the first $x$ in the $\forall$ is shadowed, in $P$,
by the second $x$ in the $\exists$.
This should be replaced by:
\[\forall x \bullet ( \dots (\exists y \bullet P[y/x]) \dots).\]
We simply check this is the case,
rather than making it so.
This is because we have no general way at present
of distinguishing substitutable and non-substitutable terms.
\textbf{Note: }
\textsf{We do now, as theories have a \texttt{SubAbilityMap} component}
\begin{code}
shadowFree :: Assertion -> Bool
shadowFree (t,sc) = shadowFree' sc S.empty t

shadowFree' :: SideCond -> VarSet -> Term -> Bool
shadowFree' sc bvs (Cons _ _ ts)    =  all (shadowFree' sc bvs) ts
shadowFree' sc bvs (Bnd _ _ vs tm) =  shadowFree'' sc bvs vs tm
shadowFree' sc bvs (Lam  _ _ vl tm) =  shadowFree'' sc bvs (S.fromList vl) tm
shadowFree' sc bvs (Cls _ tm)       =  shadowFree' sc bvs tm
shadowFree' sc bvs (Sub _ t s) =  shadowFree' sc bvs t && shadowFreeSub sc bvs s
shadowFree' _  _   asn              = True

shadowFree'' sc bvs vs tm
 | bvs `disjoint` vs  =  shadowFree' sc (bvs `S.union` vs) tm
 | otherwise          =  False

shadowFreeSub sc bvs (Substn es _)
                             =  all (shadowFree' sc bvs) $ map snd $ S.toList es
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
  = changed $ liveProofs__ del reqs
  where del = M.delete (conjThName liveProof,conjName liveProof)
\end{code}

\subsubsection{Saving a Proof}

\begin{code}
saveProof :: REqState -> LiveProof -> REqState
saveProof reqs liveProof
  = changed $ liveProofs__ upd reqs
  where upd = M.insert (conjThName liveProof,conjName liveProof) liveProof
\end{code}

\subsubsection{Completing a Proof1

\begin{code}
completeProof :: REqState -> LiveProof -> REqState
completeProof reqs liveProof
  = ( changed $ liveProofs__ del $ theories__ (upgrade . addProof) reqs )
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
        i' = if i <= 0 then 1 else i
        (ok,tz') = downTZ i' tz
    in if ok
        then return ( focus_ (tz',seq')
                    $ fPath__ (++[i'])
                    $ matches_ [] liveProof )
        else fail ("No sub-term "++show i')

\end{code}

\begin{code}
moveDownNTimes :: Monad m => Int -> Int -> LiveProof -> m LiveProof
moveDownNTimes 0 i liveProof = fail("Error ")
moveDownNTimes 1 i liveProof = moveFocusDown i liveProof
moveDownNTimes n i liveProof
  = let (tz,seq') = focus liveProof
        i' = if i <= 0 then 1 else i
        n' = if n <= 0 then 1 else n
        (ok,tz') = followTZ (replicate n' i') tz
    in if ok 
        then return ( focus_ (tz', seq')
                     $ fPath__ (++(replicate n' i'))
                     $ matches_ [] liveProof)
        else moveDownNTimes (n'-1) i' liveProof

\end{code}


\begin{code}
moveToBottom :: Monad m => Int -> LogicSig -> LiveProof -> m LiveProof
moveToBottom n theSig liveProof
    = let (tz, seq') = focus liveProof
          goalt = getTZ tz
          scC = conjSC liveProof
          ctxts = mtchCtxts liveProof
          n' = if n <= 0 then 1 else n
          (ok, tz') = downTZ n' tz
      in if ok
          then moveToBottom n' theSig (focus_ (tz', seq') $ fPath__ (++[n']) $ matches_ [] liveProof)
          else let ((thnm',lws',vts'):mcs) = ctxts
                   ((thnm,lws,vts):mcs') = mcs
                   laws = filter (\l -> lawName l == "true") lws
                   in if (length laws <= 0)
                      then  fail ("no laws of this name " ++ (lawName (lws !! 1)))
                      else let
                          law = head laws
                -- else let (law,vts) = findLaw "true" ctxts
                          matches = domatch theSig vts (goalt, scC) law
                        
                          in if (length matches <= 0)
                              then fail ("failed to match " ++ lawName law)
                              else let
                                     mtch = head matches
                                     unbound = findUnboundVars (mBind mtch) (mRepl mtch)
                                     ubind = completeUnbound unbound mtch
                                     cbind = mBind mtch `mergeBindings` ubind
                                     repl = mRepl mtch
                                     scL = snd $ mAsn mtch
                                     dpath = fPath liveProof
                                     conjpart = exitTZ tz
                                 in do scLasC <- instantiateSC cbind scL
                                       scD <- scDischarge scC scLasC
                                       if onlyFreshSC scD
                                          then do let freshneeded = snd scD
                                                  let knownVs = zipperVarsMentioned $ focus liveProof
                                                  let (fbind, fresh) = generateFreshVars knownVs freshneeded cbind
                                                  brepl <- instantiate fbind repl
                                                  scC' <- scC `mrgSideCond` freshAsSideCond fresh
                                                  return ( focus_ ((setTZ brepl tz), seq')
                                                         $ matches_ []
                                                         $ conjSC_ scC'
                                                         $ stepsSoFar__
                                                            (( UseLaw (ByMatch $ mClass mtch)
                                                                      (mName mtch)
                                                                      fbind
                                                                      dpath
                                                             , (conjpart, conjSC liveProof)):)
                                                            liveProof)
                                          else fail ("AAAAAH") 
                                      where 
                                        true = theTrue $ theSig
                                        false = theFalse $ theSig
                                        completeUnbound unbound mtch = mBind mtch
                       


       --   else case matchLawByName theSig (goalt, scC) "true" ctxts of
       --         Yes [] -> return liveProof
                --Yes mtchs -> return (focus (tz, seq') $ fPath__ (++[]) $ matches_ mtchs liveProof)
       --         Yes mtchs -> return $ matches_ mtchs liveProof
       --         But msgs -> fail $ unlines msgs






          --else let goalt = getTZ tz
          --         scC = conjSC liveProof
          --         ctxts = mtchCtxts liveProof
          --         newMatches = matchInContexts theSig ctxts (goalt, scC)
          --         rankedM = rankAndSort sizeRank ctxts
          --                     $ filter isNonTrivial newMatches
          --     in return (focus_ (tz,seq') $ fPath__ (++[]) $ matches_ rankedM liveProof)
\end{code}

The error handling for numbers less than one as path options needs to be fixed.
Firstly, this only checks the first item of the list, and secondly in the args2intList
function in Utilities, it can't accept negative numbers.
\begin{code}

followPath :: Monad m => [Int] -> LiveProof -> m LiveProof
followPath [] liveProof = fail ("No path to follow")
followPath (x:xs) liveProof
    = let (tz, seq') = focus liveProof
          x' = if x <=0 then 1 else x  --this error handling needs to be done better
          (ok, tz') = followTZ((x':xs)) tz
      in if ok
          then return ( focus_ (tz', seq')
                       $ fPath__ (++((x':xs)))
                       $ matches_ [] liveProof)
          else followPath (init (x':xs)) liveProof
\end{code}

This function moves through a proof in a depth first manner.
tryLawRecursively
domatch
recursive 
\begin{code}

trySimplifyRecursively :: Monad m => LogicSig -> LiveProof ->  m LiveProof
trySimplifyRecursively theSig liveProof 
    = let (tz, seq') = focus liveProof
          ss = listOfSubTerms tz
      in if length ss >= 0
          then trySimplifyRecursively' theSig liveProof (ss ++ [0]) 
          else fail("0")

{-
tryLawRecursively' :: Monad m => LogicSig -> LiveProof -> [Int] -> m LiveProof
tryLawRecursively' theSig liveProof (s:ss)
    = let (tz, seq') = focus liveProof
          goingDown = s > 0
      in if goingDown
          then let (ok, tz') = downTZ s tz
                   ss' = listOfSubTerms tz' ++ [0] ++ ss
               in
                   tryLawRecursively' theSig (focus_ (tz', seq') $ fPath__ (++[s]) $ matches_ [] liveProof) ss'
          else let liveProof' = (focus_ (setTZ (Val (E ArbType) $ Integer 42) tz, seq') $ fPath__ (++[]) $ matches_ [] liveProof)
                   goalt = getTZ tz
                   scC = conjSC liveProof
                   ctxts = mtchCtxts liveProof
                   ((thnm',lws',vts'):mcs) = ctxts
                   ((thnm,lws,vts):mcs') = mcs
                   laws = filter (\l -> lawName l == "equiv_refl") lws
                   --hardcoding here
                   in if (length laws <= 0)
                       then fail ("failed to match " ++ (lawName (lws !! 1)))
                       else let
                              law = head laws
                              matches = domatch theSig vts (goalt, scC) law
                              in if (length matches <= 0)
                              then let (tzNew, seqNew) = focus liveProof
                                       (ok', tz'') = upTZ tzNew
                                       in if length ss > 0
                                             then tryLawRecursively' theSig (focus_ (tz'', seqNew) $ fPath__ (++[]) $ matches_ [] liveProof) ss
                                             else return liveProof
                              else let
                                    mtch = head matches
                                    unbound = findUnboundVars (mBind mtch) (mRepl mtch)
                                    ubind = mBind mtch
                                    cbind = mBind mtch `mergeBindings` ubind
                                    repl = mRepl mtch
                                    scL = snd $ mAsn mtch
                                    dPath = fPath liveProof
                                    conjpart = exitTZ tz
                                    in do scLasC <- instantiateSC cbind scL
                                          scD <- scDischarge scC scLasC
                                          if onlyFreshSC scD
                                              then do let freshneeded = snd scD
                                                      let knownVs = zipperVarsMentioned $ focus liveProof
                                                      let (fbind, fresh) = generateFreshVars knownVs freshneeded cbind
                                                      brepl <- instantiate fbind repl
                                                      scC' <- scC `mrgSideCond` freshAsSideCond fresh
                                                      let liveProof' = (focus_ ((setTZ brepl tz), seq')
                                                                   $ matches_ []
                                                                   $ conjSC_ scC'
                                                                   $ stepsSoFar__
                                                                       (( UseLaw (ByMatch $ mClass mtch)
                                                                                 (mName mtch)
                                                                                 fbind
                                                                                 dPath
                                                                        , (conjpart, conjSC liveProof)):)
                                                                       liveProof)
                                                      let (tzNew, seqNew) = focus liveProof'
                                                      let (ok', tz2) = upTZ tzNew
                                                      if length ss >0
                                                            then tryLawRecursively' theSig (focus_ (tz2, seqNew) $ fPath__ (++[]) $ matches_ [] liveProof') ss
                                                            else return liveProof'
                                          else fail ("I'M DYING")
       {- 
                                     
                   (tzNew, seqNew) = focus liveProof'
                   (ok', tz'') = upTZ tzNew
              in if length ss > 0
                   then tryLawRecursively' theSig (focus_ (tz'', seqNew) $ fPath__ (++[]) $ matches_ [] liveProof') ss
                   else return liveProof'
         -}             

-}

simplify :: Monad m => LogicSig -> LiveProof -> [MatchContext] -> m LiveProof
simplify theSig liveProof ctxts
    = let ((thnm, lws, vts):mcs) = ctxts
          cnumber = length ctxts
          simpTheories = simplificationTheories
          simpTheory = filter(\t -> t == thnm) simpTheories
          [simpTheory'] = simpTheory
          simpLaws = simplificationLaws simpTheory'
          in if length simpLaws <= 0
                then if length mcs <= 0
                        then return liveProof
                        else simplify theSig liveProof mcs
                else do liveProof' <- simplify' theSig liveProof ctxts simpLaws
                        if length mcs <= 0
                           then return liveProof'
                           else simplify theSig liveProof' mcs

simplify' :: Monad m => LogicSig -> LiveProof -> [MatchContext] -> [String] -> m LiveProof
simplify' theSig liveProof ctxts (simpLaw:simpLaws)
    = let ((thnm,lws,vts):m) = ctxts
          [simpLaw'] = simpLaw
          laws = filter(\l -> lawName l == simpLaw) lws
          in if length laws <= 0
                then if (length simpLaws <= 0)
                     then return liveProof
                     else simplify' theSig liveProof ctxts simpLaws
                else let law = head laws
                         (tz, seq') = focus liveProof
                         goalt = getTZ tz
                         scC = conjSC liveProof
                         matches = domatch theSig vts (goalt, scC) law
                         in if (length matches <= 0)
                               then if length simpLaws <= 0
                                       then return liveProof
                                       else simplify' theSig liveProof ctxts simpLaws
                               else let mtch = head matches
                                 in if ((sizeRank ctxts mtch) > (termSize (getTZ tz)))
                                    then if length simpLaws <= 0
                                      then return liveProof
                                      else simplify' theSig liveProof ctxts simpLaws
                                    else let
                                        unbound = findUnboundVars (mBind mtch) (mRepl mtch)
                                        ubind = mBind mtch
                                        cbind = mBind mtch `mergeBindings` ubind
                                        repl = mRepl mtch
                                        scL = snd $ mAsn mtch
                                        dPath = fPath liveProof
                                        conjpart = exitTZ tz
                                        in do scLasC <- instantiateSC cbind scL
                                              scD <- scDischarge scC scLasC
                                              if onlyFreshSC scD
                                              then do let freshneeded = snd scD
                                                      let knownVs = zipperVarsMentioned $ focus liveProof
                                                      let (fbind, fresh) = generateFreshVars knownVs freshneeded cbind
                                                      brepl <- instantiate fbind repl
                                                      scC' <- scC `mrgSideCond` freshAsSideCond fresh
                                                      let liveProof' = (focus_ ((setTZ brepl tz), seq')
                                                                       $ matches_ []
                                                                       $ conjSC_ scC'
                                                                       $ stepsSoFar__
                                                                           (( UseLaw (ByMatch $ mClass mtch)
                                                                                     (mName mtch)
                                                                                     fbind
                                                                                     dPath
                                                                           , (conjpart, conjSC liveProof)):)
                                                                           liveProof)
                                                      if length simpLaws <= 0
                                                         then return liveProof'
                                                      else simplify' theSig liveProof' ctxts simpLaws
                                               else fail ("side condition issue")

trySimplifyRecursively' :: Monad m => LogicSig -> LiveProof -> [Int] -> m LiveProof
trySimplifyRecursively' theSig liveProof (s:ss)
    = let (tz, seq') = focus liveProof
          goingDown = s > 0
          in if goingDown
             then let (ok, tz') = downTZ s tz
                      ss' = listOfSubTerms tz' ++[0] ++ ss
                      in trySimplifyRecursively' theSig (focus_ (tz', seq') $ matches_ [] liveProof) ss'
             else do  let ctxts = mtchCtxts liveProof
                      liveProof' <- simplify theSig liveProof ctxts
                      let (tz, seq') = focus liveProof'
                      let (ok, tz') = upTZ tz
                      if length ss > 0
                         then trySimplifyRecursively' theSig (focus_ (tz', seq') $ matches_ [] liveProof') ss
                         else return liveProof'
                             
tryLawRecursively2 :: Monad m => LogicSig -> LiveProof -> [Int] -> m LiveProof
tryLawRecursively2 theSig liveProof (s:ss)
    = let (tz, seq') = focus liveProof
          goingDown = s > 0
          in if goingDown
             then let (ok, tz') = downTZ s tz
                      ss' = listOfSubTerms tz' ++[0] ++ ss
                      in tryLawRecursively2 theSig (focus_ (tz', seq') $ fPath__ (++[s]) $ matches_ [] liveProof) ss'
             else let goalt = getTZ tz
                      scC = conjSC liveProof
                      ctxts = mtchCtxts liveProof
                      ((thnm, lws, vts):mcs) = ctxts
                      simpTheories = simplificationTheories
                      in if length simpTheories <= 0 
                         then tryLawRecursively2 theSig liveProof ss
                         else let simpTheory = filter(\t -> t == thnm) simpTheories
                                  [simpTheory'] = simpTheory
                                  simpLaws = simplificationLaws simpTheory'
                                  in if length simpLaws <= 0
                                     then tryLawRecursively2 theSig liveProof ss
                                     else let simpLaw = head simpLaws
                                              [simpLaw'] = simpLaw
                                              laws = filter(\l -> lawName l == simpLaw) lws
                                          in if length laws <= 0
                                             then fail ("failed to match " ++ simpLaw ++ " length: " ++ (show $ length laws))
                                             else let
                                              law = head laws
                                              matches = domatch theSig vts (goalt, scC) law
                                              in if (length matches <= 0)
                                                 then let (ok', tz') = upTZ tz
                                                          in if length ss > 0
                                                             then tryLawRecursively2 theSig (focus_ (tz', seq')
                                                                                            $ fPath__ (++[])
                                                                                            $ matches_ [] liveProof) ss
                                                             else return liveProof
                                                 else let mtch = head matches
                                                          unbound = findUnboundVars (mBind mtch) (mRepl mtch)
                                                          ubind = mBind mtch
                                                          cbind = mBind mtch `mergeBindings` ubind
                                                          repl = mRepl mtch
                                                          scL = snd $ mAsn mtch
                                                          dPath = fPath liveProof
                                                          conjpart = exitTZ tz
                                                          in do scLasC <- instantiateSC cbind scL
                                                                scD <- scDischarge scC scLasC
                                                                if onlyFreshSC scD
                                                                then do let freshneeded = snd scD
                                                                        let knownVs = zipperVarsMentioned $ focus liveProof
                                                                        let (fbind, fresh) = generateFreshVars knownVs freshneeded cbind
                                                                        brepl <- instantiate fbind repl
                                                                        scC' <- scC `mrgSideCond` freshAsSideCond fresh
                                                                        let liveProof' = (focus_ ((setTZ brepl tz), seq')
                                                                                         $ matches_ []
                                                                                         $ conjSC_ scC'
                                                                                         $ stepsSoFar__
                                                                                             (( UseLaw (ByMatch $ mClass mtch)
                                                                                                       (mName mtch)
                                                                                                       fbind
                                                                                                       dPath
                                                                                             , (conjpart, conjSC liveProof)):)
                                                                                             liveProof)
                                                                        let (tz, seq') = focus liveProof'
                                                                        let (ok', tz') = upTZ tz
                                                                        if length ss > 0
                                                                        then tryLawRecursively2 theSig (focus_ (tz',seq')
                                                                                                       $ fPath__ (++[])
                                                                                                       $ matches_ [] 
                                                                                                         liveProof') ss
                                                                        else return liveProof'
                                                                else fail ("sidecondition issue")              
{-
moveThroughProofWorker :: Monad m => LiveProof -> [Int] -> m LiveProof
moveThroughProofWorker liveProof (s:ss) 
    = let (tz, seq') = focus liveProof
          goingDown = s > 0 
      in if goingDown
          then let (ok, tz') = downTZ s tz
                   ss' = listOfSubTerms tz' ++ [0] ++ ss
               in if ok
                   then moveThroughProofWorker (focus_ (tz', seq') $ fPath__ (++[s]) $ matches_ [] liveProof) (ss') 
                   else return (focus_ (tz, seq')
                               $ fPath__ (++[])
                               $ matches_ [] liveProof)      
          else let -- (tz''', seq') = (setTZ (Val (E ArbType) $ Integer 42) tz, seq')
                    (ok', tz'') = upTZ tz
          --else let (tz, seq') = (setTZ (Val (E ArbType) $ Integer 42) tz, seq')
               in if ok'
                   then moveThroughProofWorker (focus_ (tz'', seq') $ fPath__ (++[]) $ matches_ [] liveProof) (ss)
                   --else return (focus_ (tz, seq')
                   else return (focus_  (setTZ (Val (E ArbType) $ Integer 42) tz, seq')
                               $ fPath__ (++[])
                               $ matches_ [] liveProof)

-}
\end{code}

This function is just for testing in the interface
\begin{code}

checkSubTermsNumbers :: LiveProof -> String
checkSubTermsNumbers liveProof
    = show $ numOfSubTerms tz where
        (tz, seq') = focus liveProof

listOfSubTermsNumbers :: LiveProof -> String
listOfSubTermsNumbers liveProof
    = show $ listOfSubTerms tz where
        (tz, seq') = focus liveProof

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

\subsubsection{Move Up, Get and Apply Match}

\begin{code}

mUGAM :: Monad m => LogicSig -> LiveProof -> m LiveProof
mUGAM theSig liveProof
    = let (tz, seq') = focus liveProof
          (ok, tz') = upTZ tz
      in if ok
          then return ( focus_ (tz', seq')
                      $ fPath__ init
                      $ matches_ [] liveProof )
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
                    $ stepsSoFar__ ((sw',(exitTZ $ fst sz,conjSC liveProof)):)
                      liveProof )
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
                    $ stepsSoFar__ ((sw', (exitTZ $ fst sz,conjSC liveProof)):)
                      liveProof )
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
                    $ stepsSoFar__ ((sw', (exitTZ $ fst sz,conjSC liveProof)):)
                      liveProof )
        else fail "Not in hypotheses"
\end{code}

\subsubsection{Match Laws against Focus}

First, matching all laws.
\begin{code}
matchFocus :: LogicSig -> LiveProof -> LiveProof
matchFocus theSig liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  conjSC liveProof
        ctxts       =  mtchCtxts liveProof
        newMatches  =  matchInContexts theSig ctxts (goalt,scC)
        rankedM     =  rankAndSort sizeRank ctxts
                         $ filter isNonTrivial newMatches
    in matches_ rankedM liveProof
\end{code}

Second, matching a specific law.
\begin{code}
matchFocusAgainst :: Monad m => String -> LogicSig -> LiveProof -> m LiveProof
matchFocusAgainst lawnm theSig liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  conjSC liveProof
        ctxts       =  mtchCtxts liveProof
    in case matchLawByName theSig (goalt,scC) lawnm ctxts of
          Yes []    -> fail ("No matches against focus for '"++lawnm++"'")
          Yes mtchs -> return $ matches_ mtchs liveProof
          But msgs  -> fail $ unlines msgs
\end{code}

Third, a deep dive to apply \texttt{match} so we can get back errors.
\begin{code}
tryFocusAgainst :: String -> [Int] -> LogicSig -> LiveProof
                -> YesBut (Binding,Term,SideCond,SideCond)
tryFocusAgainst lawnm parts theSig liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  conjSC liveProof
        ctxts       =  mtchCtxts liveProof
    in tryLawByName theSig (goalt,scC) lawnm parts ctxts
\end{code}

\newpage
\subsubsection{Apply Match to Focus}

We have a 2-phase approach here.
First we find the match, determine what variables
in the replacement are missing from the binding,
and return those along with the match
\begin{code}
applyMatchToFocus1 :: Monad m
                   => Int -> LiveProof
                   -> m ( VarSet
                        , Match )
applyMatchToFocus1 i liveProof
  = do  mtch  <- nlookup i $ matches liveProof
        let unbound = findUnboundVars (mBind mtch) (mRepl mtch)
        return (unbound,mtch)

\end{code}

Now given the match,
and a binding for the previously unbound replacement variables ,
we proceed to fully instantiate the replacement term,
and the law side-condition.
We then try to discharge that side-condition.
If succesful, we replace the focus.
\begin{code}
applyMatchToFocus2 :: Monad m
                   => Match -> VarSet -> Binding
                   -> LiveProof -> m LiveProof
applyMatchToFocus2 mtch unbound ubind liveProof
  = let cbind = mBind mtch `mergeBindings` ubind
        repl = mRepl mtch
        scL = snd $ mAsn mtch
        scC = conjSC liveProof
        (tz,seq') = focus liveProof
        dpath = fPath liveProof
        conjpart = exitTZ tz
    in do scLasC <- instantiateSC cbind scL
          scD <- scDischarge scC scLasC
          if onlyFreshSC scD
            then do let freshneeded = snd scD
                    let knownVs = zipperVarsMentioned $ focus liveProof
                    let (fbind,fresh) = generateFreshVars knownVs freshneeded cbind
                    brepl  <- instantiate fbind repl
                    scC' <- scC `mrgSideCond` freshAsSideCond fresh
                    return ( focus_ ((setTZ brepl tz),seq')
                           $ matches_ []
                           $ conjSC_ scC'
                           $ stepsSoFar__
                              (( UseLaw (ByMatch $ mClass mtch)
                                        (mName mtch)
                                        fbind
                                        dpath
                               , (conjpart,conjSC liveProof)):)
                              liveProof )
            else fail ("Undischarged side-conditions: "++trSideCond scD)

freshAsSideCond :: VarSet -> SideCond
freshAsSideCond fresh = fromJust $ mkSideCond [] fresh
\end{code}


\subsubsection{Normalise Quantifiers}

\begin{code}
normQuantFocus :: Monad m => Theories -> LiveProof -> m LiveProof
normQuantFocus thrys liveProof
 | conjSC liveProof == scTrue
   =  let (tz,seq') = focus liveProof
          dpath = fPath liveProof
          t = getTZ tz
          t' = fst $ normaliseQuantifiers ( t, scTrue )
      in return ( focus_ ((setTZ t' tz),seq')
                 $ matches_ []
                 $ stepsSoFar__
                    (( NormQuant dpath
                     , (exitTZ tz,conjSC liveProof)):)
                    liveProof )
 | otherwise  =  fail "quant-norm: only when s.c. is true"
\end{code}


\subsubsection{Simplify Nested Quantifiers Substitution}

\begin{code}
nestSimpFocus :: Monad m => Theories -> LiveProof -> m LiveProof
nestSimpFocus thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
    in case nestSimplify t of
        Yes t' -> return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                            (( NestSimp dpath
                             , (exitTZ tz,conjSC liveProof)):)
                            liveProof )
        _      -> fail "nesting simplify only for nested (similar) quantifiers"
\end{code}

\subsubsection{Reverse Substitution}

\subsubsection{Perform Substitution}

\begin{code}
substituteFocus :: Monad m => Theories -> LiveProof -> m LiveProof
substituteFocus thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
        sams = map subable $ getTheoryDeps' (conjThName liveProof) thrys
    in case t of
         (Sub _ tm s)
            -> do t' <- substitute sams s tm
                  return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                            (( Substitute dpath
                             , (exitTZ tz,conjSC liveProof)):)
                            liveProof )
         _  -> fail "substitute only for explicit substitution focii"
\end{code}

\subsubsection{Reverse Substitution}

\begin{code}
revSubstituteFocus :: Monad m => Int -> Theories -> LiveProof -> m LiveProof
revSubstituteFocus n thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
        sams = map subable $ getTheoryDeps' (conjThName liveProof) thrys
        n' =  if n==0 then 1 else n
    in do t' <- revSubstitute sams n' t
          fail ("NYfI:revSubstituteFocus "++show n++" "++trTerm 0 t')
\end{code}


\subsubsection{Observing Laws in Scope}

\begin{code}
observeLawsInScope :: LiveProof -> String
observeLawsInScope liveProof
  = let mctxts = mtchCtxts liveProof
    in hdr ++ (intercalate hdr $ map showContextLaws $ reverse mctxts)
  where hdr = "\n---\n"
\end{code}

\subsubsection{Observing Knowns Names in Scope}

\begin{code}
observeKnownsInScope :: LiveProof -> String
observeKnownsInScope liveProof
  | null mctxts  =  "*Nothing* in scope!!!"
  | otherwise    =  showContextKnowns $ head mctxts
  where mctxts   =  mtchCtxts liveProof

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
                         $ stepsSoFar__
                                 (((Flatten opI,(exitTZ tz,conjSC liveProof))):)
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
                         $ stepsSoFar__
                            (((Associate opI gs,(exitTZ tz,conjSC liveProof))):)
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

\textbf{Note: }\textit{In fact, given that any predicate $P$
can be replaced by $P\land\true$, we can in fact do the instantiation
on any such $P$, replacing it by $P\land L_I$,
where $L_I$ is a law instantiatied
using the context of $P$.}
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
        rslaws = concat $ map snd3 $ mtchCtxts liveProof
    in if currt /= true then [] else rslaws
\end{code}

We should now get back those laws as well as the selected number.
We now get the law, and return it along with,
all the unknown free variables in the law,
and all the sub-terms of the complete proof goal.
\begin{code}
lawInstantiate2 :: Monad m
                => [Law] -> Int -> LiveProof -> m (Law,[Variable],[Term])
lawInstantiate2 rslaws i liveProof
  = do law@((lnm,(lawt,lsc)),lprov) <- nlookup i rslaws
       let (tz,seq') = focus liveProof
       let psc = conjSC liveProof
       let dpath = fPath liveProof
       let vts = concat $ map thd3 $ mtchCtxts liveProof
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
                  ( ( (UseLaw ByInstantiation lnm lbind dpath)
                    , (exitTZ tz,conjSC liveProof) ) : )
                  liveProof )

mkBinding bind [] = return bind
mkBinding bind ((v,t):rest)
  = do bind' <- bindVarToTerm v t bind
       mkBinding bind' rest
\end{code}

\newpage
\subsubsection{Clone Hypotheses}

This should only be done in an assumption strategy
that reduces all of the consequent.
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
          -> return ( focus_ (mkTZ $ PCons land [hypt,currt],seq')
                    $ matches_ []
                    $ stepsSoFar__ ((CloneH i, (exitTZ tz,conjSC liveProof)):)
                      liveProof )
\end{code}

\newpage{Equivalence Theorem from Live-Proof}

-- stepEquivalenceTheorem args
\begin{code}
stepEquivalenceTheorem :: Monad m => String -> (REqState, LiveProof)
                       -> m (Maybe String,(REqState, LiveProof))
stepEquivalenceTheorem nm state@(reqs, liveProof)
 | strat /= reduceAll
     =  return ( Just ("Not allowed from "++strat++" strategy")
               , state )
 | not (all isStraightStep $ stepsSoFar liveProof)
     =  return ( Just "Calculation cannot switch or clone"
               , state )
 | otherwise
  = let
      (thrynm,law,proof) = makeEquivalence nm liveProof
    in case getTheory thrynm (theories reqs) of
        Nothing ->  return ( Just ("Can't find theory "++thrynm)
                           ,  state )
        Just thry
          ->  let thry' = laws__ (law:) $ proofs__ (proof:) thry in
               return ( Nothing
                      , ( theories__ (replaceTheory' thry') reqs
                        , liveProof ) )
 where strat = strategy liveProof
\end{code}
