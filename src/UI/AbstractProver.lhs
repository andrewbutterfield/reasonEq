\chapter{Abstract Prover User-Interface}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2017--2025
              Saqib Zardari     2023
              Aaron Bruce       2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.AbstractProver
( REqState
, abandonProof -- prover
, updateProof -- prover 
, completeProof -- prover
, moveFocusDown -- prover
, moveFocusUp -- prover
, switchConsequentFocus -- prover
, moveFocusToHypothesis -- prover
, moveFocusFromHypothesis -- prover
, matchFocus -- prover
, matchFocusAgainst -- prover
, applyMatchToFocus1 -- prover
, applyMatchToFocus2 -- prover
, applySAT -- prover
, nestSimpFocus -- prover
, substituteFocus -- prover
, tryFocusAgainst -- prover
, tryAlphaEquiv -- prover
, observeLawsInScope -- prover
, observeTheoriesInScope -- prover
, observeKnownsInScope -- prover
, flattenAssociative -- prover
, groupAssociative -- prover
, stepBack -- prover
, lawInstantiate1 -- prover
, lawInstantiate2 -- prover
, lawInstantiate3 -- prover
, cloneHypothesis -- prover
, stepEquivalenceTheorem -- prover
)
where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Char
import Data.Maybe
import Data.List
import Control.Applicative

import NotApplicable
import YesBut
import Utilities
import UnivSets
import LexBase
import Variables
import SideCond
import Assertions
import Laws
import TermZipper
import Types
import AST
import FreeVars
import AlphaEquiv
import Substitution
import Binding
import VarData
import MatchContext
import Typing
import Instantiate
import Sequents
import ProofSettings
import UI.ClassifierTUI
import REqState
import Persistence
import ProofMatch
import Ranking
import SAT

import TestRendering
import SourceHandling

import StdTypeSignature

import Debugger
\end{code}

\section{Introduction}

This module provides the abstract functions for a live proof.

\subsection{Abandoning a Proof}

\begin{code}
abandonProof :: REqState -> LiveProof -> REqState
abandonProof reqs liveProof
  = changed $ liveProofs__ del reqs
  where del = M.delete (conjThName liveProof,conjName liveProof)
\end{code}

\subsection{Saving a Proof}

\begin{code}
updateProof :: REqState -> LiveProof -> REqState
updateProof reqs liveProof
  = changed $ liveProofs__ upd reqs
  where upd = M.insert (conjThName liveProof,conjName liveProof) liveProof
\end{code}

\subsection{Completing a Proof}

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

\section{Modifying Proof-State (\texttt{LiveProofs})}

\subsection{Moving Focus Down}

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

\subsection{Moving Focus Up}

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

\subsection{Switching Consequent Focus}

\begin{code}
switchConsequentFocus :: MonadFail m => LiveProof -> m LiveProof
switchConsequentFocus liveProof
  = let
      sz = focus liveProof
      (ok,sw',sz') = switchLeftRight sz
    in if ok
        then do let asn' = mkAsn (exitTZ $ fst sz) (conjSC liveProof)
                return ( focus_ sz'
                       $ matches_ []
                       $ fPath_ []
                       $ stepsSoFar__ ((sw', asn'):)
                         liveProof )
        else fail "Not in consequent"
\end{code}


\subsection{Focus into Hypotheses}

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
        then do let asn' = mkAsn (exitTZ $ fst sz) (conjSC liveProof)
                return ( mtchCtxts_ mcs
                       $ focus_ sz'
                       $ matches_ []
                       $ stepsSoFar__ ((sw', asn'):)
                         liveProof )
        else fail ("No hypothesis "++show i)
\end{code}

\newpage
\subsection{Return Focus from Hypotheses}

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
        then do let asn' = mkAsn (exitTZ $ fst sz) (conjSC liveProof)
                return ( mtchCtxts_ mcs
                       $ focus_ sz'
                       $ matches_ []
                       $ stepsSoFar__ ((sw', asn'):)
                         liveProof )
        else fail "Not in hypotheses"
\end{code}

\subsection{Match Laws against Focus}

In all matching cases we use a type-comparison operator that is 
the canonisisation of the sub-type relation:
\begin{code}
cSubType :: CanonicalMap -> TypCmp
cSubType = canoniseTypes isSubTypeOf
\end{code}


Matching all laws:
\begin{code}
matchFocus :: MonadFail m => Ranking -> LiveProof -> m LiveProof 
matchFocus ranking liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  xpndSC liveProof
        ctxts       =  mtchCtxts liveProof
        vts         =  getVarTables ctxts
    in do let (asn',tvmap) = mkTypedAsn vts goalt scC 
          let fits  =  cSubType tvmap
          let mtchs = matchInContexts ctxts fits asn'
          let rankedM = ranking ctxts mtchs
          return $ matches_ rankedM liveProof
  where 
    mshow m = 
      mName m 
      ++ "(" 
      ++ show (mClass m)
      ++ ")  --  "
      ++ trTerm 0 (mRepl m)
\end{code}

Matching a specific law:
\begin{code}
matchFocusAgainst :: MonadFail m => String -> LiveProof -> m LiveProof
matchFocusAgainst lawnm liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  xpndSC liveProof
        ctxts       =  mtchCtxts liveProof
        vts         =  getVarTables ctxts
    in do let (asn',tvmap) = mkTypedAsn vts goalt scC
          let fits  =  cSubType tvmap
          case matchLawByName asn' lawnm ctxts fits of
            Yes []    -> fail ("No matches against focus for '"++lawnm++"'")
            Yes mtchs -> return $ matches_ mtchs liveProof
            But msgs  -> fail $ unlines msgs
\end{code}

Third, a deep dive to apply \texttt{match} so we can get back errors.
\begin{code}
tryFocusAgainst :: String -> [Int] -> LiveProof
                -> YesBut (Binding,SideCond,Term,SideCond,SideCond)
tryFocusAgainst lawnm parts liveProof
  = let (tz,_)      =  focus liveProof
        goalt       =  getTZ tz
        scC         =  xpndSC liveProof
        ctxts       =  mtchCtxts liveProof
        vts         =  getVarTables ctxts
    in do let (asn',tvmap) = mkTypedAsn vts goalt scC
          let fits  =  cSubType tvmap
          tryLawByName asn' lawnm parts ctxts fits
\end{code}

\newpage
\subsection{Apply Match to Focus}

We have a matchLawCommand-phase approach here:
\begin{itemize}
  \item
    Return specified match with lists of floating variables
    for which there is a choice of replacements,
    along with those choices
    (\texttt{applyMatchToFocus1}).
  \item
    Provide floating replacement choices obtained from the user.
    Use these to re-instantiate the replacements 
    (in both law body and side-condition), discharge side-conditions,
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
                   -> m ( ProofMatch       -- the chosen match
                        , [Variable]  -- unresolved floating variables
                        , [Term]      -- potential variable replacements
                        , [ListVar]   -- unresolved floating list-variables
                        , VarList     -- potential general-variable replacements
                        )
applyMatchToFocus1 i liveProof
  = do  mtch  <- nlookup i $ matches liveProof
        let goal = exitTZ $ fst $ focus liveProof
        let gvars = S.toList ( mentionedVars (mRepl mtch)
                               `S.union`
                               mentionedVars goal
                               `S.union`
                               scVarSet (mLawSC mtch) )
        let (stdvars,lstvars)  =  partition isStdV gvars
        let stdFloating        =  filter isFloatingGVar stdvars
        let replTerms          =  subTerms $ assnT $ conjecture liveProof
        let (lstFloating,lstNormal)        =  partition isFloatingGVar lstvars
        let replGVars          =  lstNormal ++ map sinkGV lstFloating
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
                   -> ProofMatch
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
        mctxts = mtchCtxts liveProof
        scC = xpndSC liveProof
        obsv = getDynamicObservables vtbls
        ictxt = ICtxt obsv scC
        (tz,seq') = focus liveProof
        dpath = fPath liveProof
        conjpart = exitTZ tz
    in do let sbind = patchBinding vts lvvls cbind
          scLasC <- instantiateSC ictxt sbind scL
          scCL <- extendGoalSCCoverage obsv lvvls scLasC
          scCX <- mrgSideCond scC scCL
          scD <- scDischarge (getDynamicObservables vtbls) scCX scLasC
          if onlyFreshSC scD
            then do let freshneeded = snd scD
                    let knownVs = zipperVarsMentioned $ focus liveProof
                    -- knownVs is all variables in entire goal and sequent
                    let (fbind,fresh)
                          = generateFreshVars knownVs freshneeded sbind
                    let scC' = addFreshVars fresh $ conjSC liveProof
                    brepl  <- instTerm ictxt fbind repl
                    let asn' = mkAsn conjpart (conjSC liveProof)
                    return ( focus_ ((setTZ brepl tz),seq')
                           $ matches_ []
                           $ conjSC_ scC'
                           $ xpndSC_ (expandSideCondKnownVars mctxts scC')
                           $ stepsSoFar__
                              (( UseLaw (ByMatch $ mClass mtch)
                                        (mName mtch)
                                        fbind
                                        dpath
                               , (asn')):)
                              liveProof )
            else fail ("Undischarged side-conditions: "++trSideCond scD)
\end{code}

\newpage

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

If a floating replacement is used
in a \texttt{CoveredBy} atomic law side condition,
then we need to copy it over as a proof-local goal side-condition.
\begin{code}
extendGoalSCCoverage obsv lvvls (tvarSCs,_)
  = xtndCoverage obsv (map snd lvvls) [] (filter isCoverage tvarSCs)
  where
    isCoverage (VSC _ _ mvsC mvsCd)  
      =  mvsC /= NA || mvsCd /= NA

    xtndCoverage :: MonadFail m => VarSet
                 -> [VarList] -- floating replacements
                 -> [VarSideConds] -- extra side-conditions (so far)
                 -> [VarSideConds] -- Law coverage side-conditions
                 -> m SideCond
    xtndCoverage _ _ vscs [] = return (vscs, S.empty)
    xtndCoverage obsv ffvls vscs ((VSC gv _ mvsC mvsCd) : rest)
      | S.toList vsC `elem` ffvls

             -- DO WE NEED THIS?
             -- (Assertion conj _) = conjecture liveProof
             -- ss = S.elems $ S.map theSubscript $ S.filter isDuring
             --              $ S.map gvarWhen $ mentionedVars conj

         = do vscs' <- mrgVarConds justcov vscs  
              xtndCoverage obsv ffvls vscs' rest
      | otherwise  =  xtndCoverage obsv ffvls vscs rest
      where 
         cunion NA (The vsCd) = vsCd
         cunion (The vsC)  NA = vsC
         cunion (The vsC) (The vsCd) = vsC `S.union` vsCd
         cunion _ _ = S.empty
         vsC = mvsC `cunion` mvsCd
         justcov = VSC gv disjNA mvsC mvsCd
\end{code}

\newpage
\subsection{Apply SAT Solver to Focus}

\begin{code}
applySAT :: MonadFail m => LiveProof -> m LiveProof
applySAT liveproof 
  = do  let (tz, seq) = focus liveproof
        let goalt = getTZ tz
        (tsat,nottsat) <- satsolve goalt
        let asn = mkAsn (exitTZ tz) (conjSC liveproof)
        let stepcons = ((SAT tsat nottsat (fPath liveproof), asn) :)
        return (focus_ (setTZ (Val pred1 (Boolean tsat)) tz, seq)
                       $ stepsSoFar__ stepcons liveproof)
\end{code}

\subsection{Automate Classifier Law Usage}



\newpage
\subsection{Normalise Quantifiers}

\textbf{Deprecated. Should be done under the hood as required}

\begin{code}
normQuantFocus :: MonadFail m => TheoryDAG -> LiveProof -> m LiveProof
normQuantFocus thrys liveProof
 | conjSC liveProof == scTrue
   =  let (tz,seq') = focus liveProof
          dpath = fPath liveProof
          t = getTZ tz
          t' = fst $ normaliseQuantifiers t scTrue
      in do let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
            return ( focus_ ((setTZ t' tz),seq')
                 $ matches_ []
                 $ stepsSoFar__
                    (( NormQuant dpath
                     , (asn')):)
                    liveProof )
 | otherwise  =  fail "quant-norm: only when s.c. is true"
 -- we can soon fix this. But this should be done automatically.
\end{code}


\subsection{Simplify Nested Quantifiers Substitution}

\begin{code}
nestSimpFocus :: MonadFail m => TheoryDAG -> LiveProof -> m LiveProof
nestSimpFocus thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
    in case nestSimplify t of
        Yes t' -> do let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
                     return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                            (( NestSimp dpath
                             , (asn')):)
                            liveProof )
        _      -> fail "nesting simplify only for nested (similar) quantifiers"
\end{code}

\subsection{Reverse Substitution}

This could be done by `substituteFocus` below

\newpage
\subsection{Perform Substitution}

\begin{code}
substituteFocus :: (MonadFail m, Alternative m)
                => TheoryDAG -> LiveProof -> m LiveProof
substituteFocus thrys liveProof
  = let (tz,seq') = focus liveProof
        dpath = fPath liveProof
        t = getTZ tz
        -- vts = getVarTables $ mtchCtxts liveProof
        scC = xpndSC liveProof
        (Assertion conj _) = conjecture liveProof
        sctxt = mkSubCtxt scC $ thd3 $ head $ mtchCtxts liveProof
    in case t of
         (Sub _ tm s)
            -> do t' <- applySubst sctxt s tm
                  let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
                  return ( focus_ ((setTZ t' tz),seq')
                         $ matches_ []
                         $ stepsSoFar__
                            (( Substitute dpath
                             , (asn')):)
                            liveProof )
         _  -> fail "substitute only for explicit substitution focii"
\end{code}


\subsection{Observing Laws in Scope}

\begin{code}
observeLawsInScope :: [String] -> LiveProof -> String
observeLawsInScope [] liveProof
  = renderContextLaws $ mtchCtxts liveProof

observeLawsInScope thnms liveProof
  = renderContextLaws $ filter (wantedMCtxt thnms) $ mtchCtxts liveProof

wantedMCtxt wanted (thnm,_,_) = thnm `elem` wanted

renderContextLaws mctxts
  = hdr ++ (intercalate hdr $ map showContextLaws $ reverse mctxts)
  where hdr = "\n---\n"
\end{code}

\textbf{NOTE: }
\textsf{
 The top level match-context has all the knowns from dependent theories,
to avoid doing lookups down through the chain of theories.
It means there is no point in adding the facility(*) provided for laws for 
specifying the theories of interest.
Perhaps this is all over-engineered?
\textbf{(*) what facility?}  
}


\subsection{Observing Knowns Names in Scope}


\begin{code}
observeTheoriesInScope :: LiveProof -> String
observeTheoriesInScope liveProof
  | null mctxts  =  "*Nothing* in scope!!!"
  | otherwise    =  intercalate " " $ map fst3 mctxts
  where mctxts   =  mtchCtxts liveProof

\end{code}

\subsection{Observing Knowns Names in Scope}


\begin{code}
observeKnownsInScope :: LiveProof -> String
observeKnownsInScope liveProof
  | null mctxts  =  "*Nothing* in scope!!!"
  | otherwise    =  showContextKnowns $ head mctxts
  where mctxts   =  mtchCtxts liveProof

\end{code}


\subsection{Flattening and Grouping Associative Operators}

\begin{code}
flattenAssociative :: MonadFail m => Identifier -> LiveProof -> m LiveProof
flattenAssociative opI liveProof
  = let (tz,seq') = focus liveProof
        t = getTZ tz
    in case flattenAssoc opI t of
        But msgs -> fail $ unlines' msgs
        Yes t' -> do let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
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
        Yes t' -> do let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
                     return ( focus_ ((setTZ t' tz),seq')
                            $ matches_ []
                            $ stepsSoFar__ (((Associate opI gs,asn')):)
                            $ liveProof )
\end{code}

\subsection{Stepping back a proof step.}

\begin{code}
stepBack  :: MonadFail m => Int -> LiveProof -> m LiveProof
stepBack i liveProof
  = return $ undoCalcStep liveProof
\end{code}

\newpage
\subsection{Law Instantiation}

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
lawInstantiate1 :: LiveProof -> [Law]
lawInstantiate1 liveProof
  = let currt = getTZ $ fst $ focus liveProof
        true = theTrue
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
       let vts = getVarTables $ mtchCtxts liveProof
       let lFreeV = stdVarSetOf $ S.filter (isUnknownGVar vts)
                                $ theFreeVars $ freeVars lsc lawt
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
       let ictxt = mkInsCtxt vts scC
       ilsc <- instantiateSC ictxt lbind lsc
       let (Assertion conj _) = conjecture liveProof
       let ss = S.elems $ S.map theSubscript $ S.filter isDuring
                        $ S.map gvarWhen $ mentionedVars conj
       nsc <- mrgSideCond scC ilsc
       ilawt <- instTerm ictxt lbind lawt
       let (tz,seq') = focus liveProof
       let dpath = fPath liveProof
       let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
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

Invoke $\alpha$-equivalence LHS/RHS check with details
\begin{code}
tryAlphaEquiv :: LiveProof -> YesBut (Map GenVar GenVar)
tryAlphaEquiv liveProof
  = let sequent = exitSeqZipper $ focus liveProof 
    in tryAlphaEquivalence (cleft sequent) (cright sequent)
\end{code}


\newpage
\subsection{Clone Hypotheses}

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
          -> do let asn' = mkAsn (exitTZ tz) (conjSC liveProof)
                return ( focus_ (mkTZ $ Cons arbpred True land [hypt,currt],seq')
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
