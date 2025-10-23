\chapter{Abstract Top-Level User-Interface}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2017--2025
              Saqib Zardari     2023
              Aaron Bruce       2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module UI.AbstractTop
( REqState
, observeSig -- top
, observeTheories -- top
, observeTheoryNames -- top
, observeLaws -- top
, observeKnowns -- top
, observeCurrTheory -- top
, observeCurrConj -- top
, observeLiveProofs -- top
, observeCompleteProofs -- top
, setCurrentTheory -- top
, showCurrentTheory -- top
, newConjecture -- top
, readConjecture -- top
, assumeConjecture -- top
, demoteLaw -- top
, classifyLaw -- top
, newProof1 -- top
, newProof2 -- top
, resumeProof -- UNUSED -- implemented directly in TopTUI
, observeSettings -- both       ----v ?
, modifyProofSettings -- both    ----^ ?
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
import RunClassified
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

This module provideds abstract functions for the \reasonEq\ top-level,
that include launching proofs. 
Live proof functions are in a separate module (\h{AbstractProver})


\subsection{Observing Current Logic}

\begin{code}
observeSig :: REqState -> String
observeSig reqs = showLogic $ reqs
\end{code}

\subsection{Observing Theories}

\begin{code}
observeTheories :: REqState -> String
observeTheories reqs = showTheories $ theories reqs

observeTheoryNames :: REqState -> String
observeTheoryNames reqs
  | null thnames  =  "<none>"
  | otherwise     =  thnames 
  where 
    thnames = intercalate " ; " $ map thName $ getAllTheories $ theories reqs
\end{code}

\subsection{Observing Laws (and Conjectures)}

\begin{code}
observeLaws :: REqState -> [String] -> String
observeLaws reqs ["-u"]  =  observe_laws reqs (trTermU 0, trSideCondU)
observeLaws reqs _       =  observe_laws reqs (trTerm 0,  trSideCond )
observe_laws reqs renderers
  -- = let thrys = getAllTheories $ theories reqs
  = let thrys = getTheoryDeps' (currTheory reqs) $ theories reqs
    in hdr ++ (intercalate hdr $ map (showTheoryLaws renderers) $ reverse thrys)
  where hdr = "\n---\n"
\end{code}

\subsection{Observing Known Names}

\begin{code}
observeKnowns :: REqState -> [String] -> String
observeKnowns reqs _
  = let thrys = getTheoryDeps' (currTheory reqs) $ theories reqs
    in hdr ++ (intercalate hdr $ map showTheoryKnowns thrys)
  where hdr = "\n---\n"
\end{code}


\subsection{Observing Current Theory}

\begin{code}
observeCurrTheory :: REqState -> String
observeCurrTheory reqs
 = case getCurrentTheory reqs of
     Nothing    ->  "No current theory."
     Just thry  ->  showTheoryLong (trTerm 0, trSideCond) thry
\end{code}

\subsection{Observing Current Conjectures}

\begin{code}
observeCurrConj :: REqState -> [String] -> String
observeCurrConj reqs ["-u"]
  = case getCurrentTheory reqs of
      Nothing    ->  "No current theory."
      Just thry  ->  showNmdAssns (trTermU 0, trSideCondU) $ conjs thry
observeCurrConj reqs _
  = case getCurrentTheory reqs of
      Nothing    ->  "No current theory."
      Just thry  ->  showNmdAssns (trTerm 0, trSideCond) $ conjs thry
\end{code}

\subsection{Observing Live Proofs}

\begin{code}
observeLiveProofs :: REqState -> String
observeLiveProofs reqs = showLiveProofs $ liveProofs reqs
\end{code}


\subsection{Observing Completed Proofs}

\begin{code}
observeCompleteProofs :: [String] -> REqState -> String
observeCompleteProofs ["*"] reqs
  = showProofs [] $ concat $ map proofs $ getAllTheories $ theories reqs
observeCompleteProofs [nm] reqs
  = showProofs [nm] $ concat $ map proofs $ getAllTheories $ theories reqs
observeCompleteProofs args reqs
  = case getCurrentTheory reqs of
      Nothing    ->  "No current theory."
      Just thry  ->  showProofs args $ proofs thry
\end{code}

\section{Modifying Proof-State (\texttt{REqState})}


\subsection{Setting Current Theory}

\begin{code}
setCurrentTheory :: MonadFail m => String -> REqState -> m REqState
setCurrentTheory thnm reqs
  = case getTheory thnm $ theories reqs of
      Nothing  ->  fail ("No theory named '"++thnm++"'.")
      Just _   ->  return ( changed $ currTheory_ thnm reqs)
\end{code}
Sometimes we want to show the current theory,
after a command that has modified it.
\begin{code}
showCurrentTheory :: MonadFail m => String -> REqState -> m String
showCurrentTheory thnm reqs
  = case getTheory thnm $ theories reqs of
      Nothing  ->  fail ("No theory named '"++thnm++"'.")
      Just thry   ->  return (showTheoryLong (trTerm 0, trSideCond) thry)
\end{code}


\newpage
\subsection{Adding a new conjecture}

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

\subsection{Load a Conjecture}

We expect the first line of a conjecture text to be the conjecture name,
while the rest is then parsed for the actual conjecture term.

\begin{code}
readConjecture :: MonadFail m => String -> REqState -> m REqState
readConjecture text reqs
  | null body = fail "no conjecture term found"
  | otherwise = 
      case loadTerm body of
        Yes (term,resttoks)
          | null resttoks -> do
              thry <- getCurrentTheory reqs
              let newasn = mkAsn term scTrue
              let newconj = (cname,newasn)
              let thry' = conjs__ ([newconj]++) thry
              thrys <- replaceTheory'' thry' $ theories reqs
              return $ changed $ theories_ thrys reqs 
          | otherwise -> fail ("junk at end: "++show resttoks)
        But msgs -> fail ("conjecture parse failed:\n"++unlines' msgs)
  where
    (cname,rest) = span (/= '\n') text
    body = ttail rest
\end{code}


\subsection{Assuming Conjectures}

\begin{code}
assumeConjecture :: MonadFail m => String -> [String] -> REqState -> m REqState
assumeConjecture thnm args reqs
  = case getTheory thnm (theories reqs) of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry  ->  doAssumption thnm thry args reqs

doAssumption thnm thry [arg1,arg2] reqs
  | all isDigit arg1 && all isDigit arg2
      = do thry' <- assumeConjRange (read arg1) (read arg2) thry
           return $ changed $ theories__ (replaceTheory' thry') $ reqs 
doAssumption thnm thry args reqs
  | whichC == "*"
      = do thys' <- assumeDepConj thnm thys
           return $ changed $ theories_ thys' reqs
  | otherwise
      = do thry' <- assumeConj whichC thry
           return $ changed $ theories__ (replaceTheory' thry') $ reqs
  where
    whichC = args2str args
    thys = theories reqs
\end{code}

\subsection{Demoting Laws}

\begin{code}
demoteLaw :: MonadFail m => String -> String -> REqState -> m REqState
demoteLaw thnm whichL reqs
  = case getTheory thnm $ theories reqs of
      Nothing -> fail ("No theory named '"++thnm++"'.")
      Just thry -> do thry' <- lawDemote whichL thry
                      return $ changed
                             $ theories__ (replaceTheory' thry') $ reqs
\end{code}

\newpage
\subsection{Classifying Laws}

\begin{code}
getLaws :: MonadFail m => Theory -> String -> m [Law]
getLaws thry lnm
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
        | whichL == "*"  ->  do 
            thys' <- lawDepClassify thnm thys
            return $ changed $ theories_ thys' reqs
        | otherwise  ->  do 
            case getLaws thry whichL of
              Nothing -> fail ("No law named '"++whichL++"' in theory.")
              Just lws -> do  
                thry' <- lawClassify lws thry
                return $ changed $ theories__ (replaceTheory' thry') $ reqs
    where thys = theories reqs
\end{code}


\subsection{Demoting Laws}

\subsection{Starting a Proof}

This is not a single abstract UI call,
but rather a series of calls, with all but the last
returning various items that need to be used by the concrete UI
to collect arguments for the next call.

\begin{code}
newProof1 :: MonadFail m => NmdAssertion -> REqState
          -> m ( NmdAssertion
               , [(String,Sequent)] ) -- named strategy list
newProof1 nconj@(nm,asn) reqs
  | shadowFree asn  =  return ( nconj
                              , availableStrategies thys currTh nconj )
  | otherwise       =  fail "shadowed bound-vars. in conjecture"
  where
    currTh = currTheory reqs
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys

newProof2 :: MonadFail m => NmdAssertion -> (String,Sequent) -> REqState
          -> m LiveProof
newProof2 (nm,asn) seqnt reqs
  = return $ launchProof thylist psettings currTh nm asn seqnt
  where
    psettings = prfSettings reqs
    currTh = currTheory reqs
    getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
    thys = theories reqs
    thylist = fromJust $ getTheoryDeps currTh thys
\end{code}

\newpage
\section{Removing Bound Variable ``Shadowing''}

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

\subsection{Resuming a Proof}

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

\subsection{Proof Settings}

These are accessed by both the top-level and prover UIs.

\begin{code}
observeSettings :: ProofSettings -> String
observeSettings pset = showPrfSettings pset
\end{code}

\begin{code}
modifyProofSettings :: MonadFail m => [String] -> ProofSettings -> m ProofSettings
modifyProofSettings [name,value] prfset
  = case changePrfSettings name value prfset of
      But msgs  ->  fail $ unlines' msgs
      Yes set'  ->  return set'
modifyProofSettings args reqs = fail "Expected setting short name and value"
\end{code}

