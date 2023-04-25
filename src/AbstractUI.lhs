\section{Abstract User-Interface}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module AbstractUI
( REqState
, observeSettings
, observeSig, observeTheories, observeTheoryNames, observeLaws
, observeKnowns
, observeCurrTheory, observeCurrConj
, observeLiveProofs, observeCompleteProofs
, modifySettings
, setCurrentTheory
, newConjecture
, assumeConjecture, demoteLaw , classifyLaw
, newProof1, newProof2, resumeProof
, abandonProof, saveProof, completeProof
, moveFocusDown, moveFocusUp, moveConsequentFocus
, moveFocusToHypothesis, moveFocusFromHypothesis
, matchFocus, matchFocusAgainst
, applyMatchToFocus1, applyMatchToFocus2
, applySAT
, applyTest
, normQuantFocus
, nestSimpFocus
, substituteFocus
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
import SAT

import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
tdbg nm t = trace (nm++" = "++trTerm 0 t) t
scdbg nm sc = trace (nm++" = "++trSideCond sc) sc
bdbg nm b = trace (nm++" = "++trBinding b) b
vsdbg nm vs = trace (nm++" = "++trVSet vs) vs
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

\subsubsection{Observing Settings}

\begin{code}
observeSettings :: REqState -> String
observeSettings reqs = showSettings $ settings reqs
\end{code}

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
observeCompleteProofs ["*"] reqs
  = showProofs [] $ concat $ map proofs $ getAllTheories $ theories reqs
observeCompleteProofs [nm] reqs
  = showProofs [nm] $ concat $ map proofs $ getAllTheories $ theories reqs
observeCompleteProofs args reqs
  = case getTheory (currTheory reqs) (theories reqs) of
      Nothing    ->  "No current theory."
      Just thry  ->  showProofs args $ proofs thry
\end{code}

\subsection{Modifying Proof-State (\texttt{REqState})}

\subsubsection{Modifying Settings}

\begin{code}
modifySettings :: MonadFail m => [String] -> REqState -> m REqState
modifySettings [name,value] reqs
  = case changeSettings name value (settings reqs) of
      But msgs  ->  fail $ unlines' msgs
      Yes set'  ->  return $ settings_ set' reqs
modifySettings args reqs = fail "Expected setting short name and value"
\end{code}

\subsubsection{Setting Current Theory}

\begin{code}
setCurrentTheory :: MonadFail m => String -> REqState -> m REqState
setCurrentTheory thnm reqs
  = case getTheory thnm $ theories reqs of
      Nothing  ->  fail ("No theory named '"++thnm++"'.")
      Just _   ->  return ( changed $ currTheory_ thnm reqs)
\end{code}

\subsubsection{Adding a new conjecture}

Easy, so long as we check for name clashes.
\begin{code}
newConjecture :: MonadFail m => String -> NmdAssertion -> REqState
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
assumeConjecture :: MonadFail m => String -> String -> REqState -> m REqState
assumeConjecture thnm whichC reqs
  = case getTheory thnm thys of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry
        | whichC == "*"
            ->  do thys' <- assumeDepConj thnm thys
                   return $ changed $ theories_ thys' reqs
        | otherwise
            ->  do thry' <- assumeConj whichC thry
                   return $ changed $ theories__ (replaceTheory' thry') $ reqs
  where thys = theories reqs
\end{code}

\subsubsection{Demoting Laws}

\begin{code}
demoteLaw :: MonadFail m => String -> String -> REqState -> m REqState
demoteLaw thnm whichL reqs
  = case getTheory thnm $ theories reqs of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry -> do thry' <- lawDemote whichL thry
                      return $ changed
                             $ theories__ (replaceTheory' thry') $ reqs
\end{code}


\subsubsection{Classifying Laws}

\begin{code}
findLaw :: MonadFail m => Theory -> String -> m [Law]
findLaw thry lnm
 | lnm == "."      =  return lwsCur
 | null law1       =  fail ("law '"++lnm++"': not found")
 | otherwise       =  return [theLaw]
 where
   lwsCur = laws thry
   (_,law1,_) = extract (((lnm==) . fst) .fst) lwsCur
   theLaw = head law1


classifyLaw :: MonadFail m => String -> String -> REqState -> m REqState
classifyLaw thnm whichL reqs
  = case getTheory thnm $ theories reqs of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry 
        | whichL == "*"
            ->  do thys' <- lawDepClassify thnm thys
                   return $ changed $ theories_ thys' reqs
        | otherwise
            ->  do case findLaw thry whichL of
                      Nothing -> fail ("No law named '"++whichL++"' in theory.")
                      Just law -> do thry' <- lawClassify law thry
                                     return $ changed
                                            $ theories__ (replaceTheory' thry') $ reqs
    where thys = theories reqs
\end{code}


\subsubsection{Demoting Laws}

\subsubsection{Starting a Proof}

This is not a single abstract UI call,
but rather a series of calls, with all but the last
returning various items that need to be used by the concrete UI
to collect arguments for the next call.

\begin{code}
newProof1 :: MonadFail m => Int -> REqState
          -> m ( NmdAssertion
               , [(String,Sequent)] ) -- named strategy list
newProof1 i reqs
  = case nlookup i' (getCurrConj reqs) of
      Nothing  ->  fail "invalid conjecture number"
      Just nconj@(nm,asn)
        | shadowFree asn
            -> return
                ( nconj
                , availableStrategies (logicsig reqs) thys currTh nconj )
        | otherwise -> fail "shadowed bound-vars. in conjecture"
  where
    i' = if i == 0 then 1 else i
    currTh = currTheory reqs
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys

newProof2 :: MonadFail m => NmdAssertion -> [(String,Sequent)] -> Int -> REqState
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

\textbf{Note:}
\textit{
This is now ensured in any Assertion by construction.
We retain it temporarily as a double-check.
}
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
shadowFree (Assertion t sc) = shadowFree' sc S.empty t

shadowFree' :: SideCond -> VarSet -> Term -> Bool
shadowFree' sc bvs (Cons _ _ _ ts)   =  all (shadowFree' sc bvs) ts
shadowFree' sc bvs (Bnd _ _ vs tm)   =  shadowFree'' sc bvs vs tm
shadowFree' sc bvs (Lam  _ _ vl tm)  =  shadowFree'' sc bvs (S.fromList vl) tm
shadowFree' sc bvs (Cls _ tm)        =  shadowFree' sc bvs tm
shadowFree' sc bvs (Sub _ t s)       =  shadowFree' sc bvs t
                                        && shadowFreeSub sc bvs s
shadowFree' _  _   asn               =  True

shadowFree'' sc bvs vs tm
 | bvs `disjoint` vs  =  shadowFree' sc (bvs `S.union` vs) tm
 | otherwise          =  False

shadowFreeSub sc bvs (Substn es _)
                             =  all (shadowFree' sc bvs) $ map snd $ S.toList es
\end{code}

\subsubsection{Resuming a Proof}

\begin{code}
resumeProof :: MonadFail m => Int -> REqState -> m LiveProof
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

\subsubsection{Completing a Proof}

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
moveFocusDown :: MonadFail m => Int -> LiveProof -> m LiveProof
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

\subsubsection{Moving Focus Up}

\begin{code}
moveFocusUp :: MonadFail m => LiveProof -> m LiveProof
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
moveConsequentFocus :: MonadFail m => LiveProof -> m LiveProof
moveConsequentFocus liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = switchLeftRight sz
    in if ok
        then do asn' <- mkAsn (exitTZ $ fst sz) (conjSC liveProof)
                return ( focus_ sz'
                       $ matches_ []
                       $ stepsSoFar__ ((sw', asn'):)
                         liveProof )
        else fail "Not in consequent"
\end{code}


\subsubsection{Focus into Hypotheses}

\begin{code}
moveFocusToHypothesis :: MonadFail m => Int -> LiveProof -> m LiveProof
moveFocusToHypothesis i liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = seqGoHyp i sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok
        then do asn' <- mkAsn (exitTZ $ fst sz) (conjSC liveProof)
                return ( mtchCtxts_ mcs
                       $ focus_ sz'
                       $ matches_ []
                       $ stepsSoFar__ ((sw', asn'):)
                         liveProof )
        else fail ("No hypothesis "++show i)
\end{code}

\newpage
\subsubsection{Return Focus from Hypotheses}

\begin{code}
moveFocusFromHypothesis :: MonadFail m => LiveProof -> m LiveProof
moveFocusFromHypothesis liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = seqLeaveHyp sz
      (_,seq') = sz'
      hthry' = getHypotheses seq'
      mcs = buildMatchContext (hthry':ante0 seq')
    in if ok
        then do asn' <- mkAsn (exitTZ $ fst sz) (conjSC liveProof)
                return ( mtchCtxts_ mcs
                       $ focus_ sz'
                       $ matches_ []
                       $ stepsSoFar__ ((sw', asn'):)
                         liveProof )
        else fail "Not in hypotheses"
\end{code}

\subsubsection{Match Laws against Focus}

First, matching all laws.
\begin{code}
matchFocus :: LogicSig -> Ranking -> LiveProof -> LiveProof -- needs to be monadic
matchFocus theSig ranking liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  conjSC liveProof
        ctxts       =  mtchCtxts liveProof
        asn'        =  fromJust $ mkAsn goalt scC -- need to fix
        newMatches  =  matchInContexts theSig ctxts asn'
        rankedM     =  ranking ctxts newMatches
    in matches_ rankedM liveProof
\end{code}

Second, matching a specific law.
\begin{code}
matchFocusAgainst :: MonadFail m => String -> LogicSig -> LiveProof -> m LiveProof
matchFocusAgainst lawnm theSig liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  conjSC liveProof
        ctxts       =  mtchCtxts liveProof
    in do asn' <- mkAsn goalt scC
          case matchLawByName theSig asn' lawnm ctxts of
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
    in do asn' <- mkAsn goalt scC
          tryLawByName theSig asn' lawnm parts ctxts
\end{code}

\newpage
\subsubsection{Apply Match to Focus}

We have a matchLawCommand-phase approach here:
\begin{itemize}
  \item
    Return specified match with lists of floating variables
    for which there is a choice of replacements,
    along with those choices
    (\texttt{applyMatchToFocus1}).
  \item
    Provide floating replacement choices obtained from the user.
    Use these to re-instantiate the replacements (in both law body and side-condition), discharge side-conditions,
    and update the focus
    (\texttt{applyMatchToFocus2}).
\end{itemize}


First we find the match and determine what variables
in the replacement are floating,
identify their possible replacements,
and return those along with the match.
\begin{code}
applyMatchToFocus1 :: MonadFail m
                   => Int -> LiveProof
                   -> m ( Match       -- the chosen match
                        , [Variable]  -- unresolved floating variables
                        , [Term]      -- potential variable replacements
                        , [ListVar]   -- unresolved floating list-variables
                        , VarList     -- potential general-variable replacements
                        )
applyMatchToFocus1 i liveProof
  = do  mtch  <- nlookup i $ matches liveProof
        let gvars = S.toList ( mentionedVars (mRepl mtch)
                               `S.union`
                               scGVars (mLawSC mtch) )
        let (stdvars,lstvars)  =  partition isStdV gvars
        let stdFloating        =  filter isFloatingGVar stdvars
        let replTerms          =  subTerms $ assnT $ conjecture liveProof
        let lstFloating        =  filter isFloatingGVar lstvars
        let replGVars          =  map sinkGV (stdFloating ++ lstFloating)
        return ( mtch
               , stdVarsOf stdFloating, replTerms
               , listVarsOf lstFloating, replGVars )
\end{code}

\newpage
We take the chosen new match pairs,
integrate them into the match,
apply them to the replacements and side-conditions.
We then try to discharge the side-condition.
If successful, we replace the focus.
\begin{code}
applyMatchToFocus2 :: MonadFail m => [VarTable]
                   -> Match
                   -> [(Variable,Term)]   -- floating Variables -> Term
                   -> [(ListVar,VarList)] -- floating ListVar -> VarList
                   -> LiveProof -> m LiveProof
applyMatchToFocus2 vtbls mtch vts lvvls liveProof
  -- need to use vts and lvvls to update mtch and process law side-conditions
  = let cbind = mBind mtch -- need to update mBind mtch, but maybe later?
        repl = mLawPart mtch
        scL = snd $ mAsn mtch
        (Assertion conj _) = conjecture liveProof
        ss = S.elems $ S.map theSubscript $ S.filter isDuring
                     $ S.map gvarWhen $ mentionedVars conj
        ictxt = mkInsCtxt ss
        scC = conjSC liveProof
        (tz,seq') = focus liveProof
        dpath = fPath liveProof
        conjpart = exitTZ tz
    in do let sbind = patchBinding vts lvvls cbind
          scLasC <- instantiateSC ictxt sbind scL
          scCL <- extendGoalSCCoverage ss lvvls scLasC
          scCX <- mrgSideCond ss scC scCL
          scD <- scDischarge ss scCX scLasC
          if onlyFreshSC scD
            then do let freshneeded = snd scD
                    let knownVs = zipperVarsMentioned $ focus liveProof
                    -- knownVs is all variables in entire goal and sequent
                    let (fbind,fresh)
                                   = generateFreshVars knownVs freshneeded sbind
                    let newLocalASC = fst scD
                    -- newLocalSC <- mkSideCond newLocalASC fresh
                    newLocalSC <- mkSideCond ss newLocalASC S.empty
                    -- Why do we ignore `fresh`?
                    -- Because we have made it so above?
                    scC' <- mrgSideCond ss scCX newLocalSC
                    brepl  <- instantiate ictxt fbind repl
                    asn' <- mkAsn conjpart (conjSC liveProof)
                    return ( focus_ ((setTZ brepl tz),seq')
                           $ matches_ []
                           $ conjSC_ scC'
                           $ stepsSoFar__
                              (( UseLaw (ByMatch $ mClass mtch)
                                        (mName mtch)
                                        fbind
                                        dpath
                               , (asn')):)
                              liveProof )
            else fail ("Undischarged side-conditions: "++trSideCond scD)
\end{code}

\begin{code}
applySAT :: (Monad m, MonadFail m) => LiveProof -> m LiveProof
applySAT liveproof = do
    let (tz, seq) = focus liveproof
    let goalt = getTZ tz
    let invertedt = negateTerm goalt
    asn <- mkAsn (exitTZ tz) (conjSC liveproof)
    case dpll goalt ["Attempting to prove the goal term to be satisfiable"] of
        (True, sxt) -> case dpll invertedt (sxt ++ ["We have proven the goal term to be satisifable. Now we will attempt to prove its negation to be satisfiable"]) of
                      (True, sxt') -> fail "The focus term is neither a tautology or a contradiction"
                      (False, sxf') -> do
                          return (focus_ ((setTZ (Val P (Boolean True)) tz), seq)
                                $ stepsSoFar__ ((SAT sxf' (fPath liveproof), asn) :) liveproof)
        (False, sxf) -> do
            return (focus_ ((setTZ (Val P (Boolean False)) tz), seq)
                  $ stepsSoFar__ ((SAT sxf (fPath liveproof), asn) :) liveproof)


\end{code}

\begin{code}
applyTest :: LiveProof -> LiveProof
applyTest liveproof =    let (tz,seq)   =  focus liveproof
                             goalt      =  getTZ tz
                         in case unsupportedOps goalt of
                            True -> trace ("True") liveproof
                            False -> trace ("False") liveproof
\end{code}

Here we replace floating variables in the \emph{range} of the binding
by the replacements just chosen by the user.
\begin{code}
patchBinding :: [(Variable,Term)]   -- floating Variables -> Term
             -> [(ListVar,VarList)] -- floating ListVar -> VarList
             -> Binding -> Binding
patchBinding [] [] bind = bind
patchBinding ((v,t):vts) lvvls bind
  = patchBinding vts lvvls $ patchVarBind v t bind
patchBinding vts ((lv,vl):lvvls) bind
  = patchBinding vts lvvls $ patchVarListBind lv vl bind
\end{code}

\newpage

If a floating replacement is used
in a \texttt{CoveredBy} atomic law side condition,
then we need to copy it over as a proof-local goal side-condition.
\begin{code}
extendGoalSCCoverage ss lvvls (atmSCs,_)
  = xtndCoverage ss (map snd lvvls) [] (filter isCoverage atmSCs)
  where
    isCoverage (CoveredBy _ _ _)  =  True
    isCoverage _                  =  False

    xtndCoverage :: MonadFail m => [Subscript]
                 -> [VarList] -- floating replacements
                 -> [AtmSideCond] -- extra side-conditions (so far)
                 -> [AtmSideCond] -- Law coverage side-conditions
                 -> m SideCond
    xtndCoverage _ _ ascs [] = return (ascs, S.empty)
    xtndCoverage ss ffvls ascs (cov@(CoveredBy _ gv vs) : rest)
      | S.toList vs `elem` ffvls

             -- DO WE NEED THIS?
             -- (Assertion conj _) = conjecture liveProof
             -- ss = S.elems $ S.map theSubscript $ S.filter isDuring
             --              $ S.map gvarWhen $ mentionedVars conj

         = do ascs' <- mrgAtmCond ss cov ascs  -- Subscripts?
              xtndCoverage ss ffvls ascs' rest
      | otherwise  =  xtndCoverage ss ffvls ascs rest
\end{code}

\newpage
\subsubsection{Normalise Quantifiers}

\textbf{Deprecated. Should be done under the hood as required}

\begin{code}
normQuantFocus :: MonadFail m => Theories -> LiveProof -> m LiveProof
normQuantFocus thrys liveProof
 | conjSC liveProof == scTrue
   =  let (tz,seq') = focus liveProof
          dpath = fPath liveProof
          t = getTZ tz
          t' = fst $ normaliseQuantifiers t scTrue
      in do asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
            return ( focus_ ((setTZ t' tz),seq')
                 $ matches_ []
                 $ stepsSoFar__
                    (( NormQuant dpath
                     , (asn')):)
                    liveProof )
 | otherwise  =  fail "quant-norm: only when s.c. is true"
 -- we can soon fix this. But this should be done automatically.
\end{code}


\subsubsection{Simplify Nested Quantifiers Substitution}

\begin{code}
nestSimpFocus :: MonadFail m => Theories -> LiveProof -> m LiveProof
nestSimpFocus thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
    in case nestSimplify t of
        Yes t' -> do asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
                     return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                            (( NestSimp dpath
                             , (asn')):)
                            liveProof )
        _      -> fail "nesting simplify only for nested (similar) quantifiers"
\end{code}

\subsubsection{Reverse Substitution}

\subsubsection{Perform Substitution}

\begin{code}
substituteFocus :: MonadFail m => Theories -> LiveProof -> m LiveProof
substituteFocus thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
        -- vts = concat $ map thd3 $ mtchCtxts liveProof
        scC = conjSC liveProof
        (Assertion conj _) = conjecture liveProof
        ss = S.elems $ S.map theSubscript $ S.filter isDuring
                     $ S.map gvarWhen $ mentionedVars conj
        sctxt = mkSubCtxt scC ss
    in case t of
         (Sub _ tm s)
            -> do t' <- substitute sctxt s tm
                  asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
                  return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                            (( Substitute dpath
                             , (asn')):)
                            liveProof )
         _  -> fail "substitute only for explicit substitution focii"
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
flattenAssociative :: MonadFail m => Identifier -> LiveProof -> m LiveProof
flattenAssociative opI liveProof
  = let (tz,seq') = focus liveProof
        t = getTZ tz
    in case flattenAssoc opI t of
        But msgs -> fail $ unlines' msgs
        Yes t' -> do asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
                     return ( focus_ ((setTZ t' tz),seq')
                            $ matches_ []
                            $ stepsSoFar__ (((Flatten opI,asn')):)
                            $ liveProof )
\end{code}


\begin{code}
groupAssociative :: MonadFail m => Identifier -> GroupSpec -> LiveProof
                 -> m LiveProof
groupAssociative opI gs liveProof
  = let (tz,seq') = focus liveProof
        t = getTZ tz
    in case groupAssoc opI gs t of
        But msgs -> fail $ unlines' msgs
        Yes t' -> do asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
                     return ( focus_ ((setTZ t' tz),seq')
                            $ matches_ []
                            $ stepsSoFar__ (((Associate opI gs,asn')):)
                            $ liveProof )
\end{code}

\subsubsection{Stepping back a proof step.}

\begin{code}
stepBack  :: MonadFail m => Int -> LiveProof -> m LiveProof
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
lawInstantiate2 :: MonadFail m
                => [Law] -> Int -> LiveProof -> m (Law,[Variable],[Term])
lawInstantiate2 rslaws i liveProof
  = do law@((lnm,asn),lprov) <- nlookup i rslaws
       let (lawt,lsc) = unwrapASN asn
       let (tz,seq') = focus liveProof
       let psc = conjSC liveProof
       let dpath = fPath liveProof
       let vts = concat $ map thd3 $ mtchCtxts liveProof
       let lFreeV = stdVarSetOf $ S.filter (isUnknownGVar vts)
                                $ theFreeVars $ freeVars lawt
       let goalTerms = reverse $ subTerms (exitTZ tz)
       return (law,S.toList lFreeV,goalTerms)
\end{code}

We now get back a pairing of each law unknown free-variable
with one of the goal sub-terms, as well as the chosen law.
This gives us enough to complete the instantiation.
\begin{code}
lawInstantiate3 :: MonadFail m => [VarTable]
                -> Law -> [(Variable,Term)] -> LiveProof -> m LiveProof
lawInstantiate3 vts law@((lnm,(Assertion lawt lsc)),lprov) varTerms liveProof
  = do lbind <- mkBinding emptyBinding varTerms
       let scC = conjSC liveProof
       let ictxt = mkInsCtxt []  -- should be ss ?
       ilsc <- instantiateSC ictxt lbind lsc
       let (Assertion conj _) = conjecture liveProof
       let ss = S.elems $ S.map theSubscript $ S.filter isDuring
                        $ S.map gvarWhen $ mentionedVars conj
       nsc <- mrgSideCond ss scC ilsc
       ilawt <- instantiate ictxt lbind lawt
       let (tz,seq') = focus liveProof
       let dpath = fPath liveProof
       asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
       return ( focus_ (setTZ ilawt tz,seq')
                $ stepsSoFar__
                  ( ( (UseLaw ByInstantiation lnm lbind dpath)
                    , (asn') ) : )
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
cloneHypothesis :: MonadFail m => Int -> Identifier -> LiveProof -> m LiveProof
cloneHypothesis i land liveProof
  = let
      (tz,seq') = focus liveProof
      hypos = laws $ getHypotheses seq'
      currt = exitTZ tz
    in case nlookup i hypos of
        Nothing -> fail ("No such hypothesis: "++show i)
        Just ((_,(Assertion hypt _)),_)
          -> do asn' <- mkAsn (exitTZ tz) (conjSC liveProof)
                return ( focus_ (mkTZ $ PCons True land [hypt,currt],seq')
                       $ matches_ []
                       $ stepsSoFar__ ((CloneH i, asn'):)
                         liveProof )
\end{code}

\newpage{Equivalence Theorem from Live-Proof}

-- stepEquivalenceTheorem args
\begin{code}
stepEquivalenceTheorem :: MonadFail m => String -> (REqState, LiveProof)
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
