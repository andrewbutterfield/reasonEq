\section{Live Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LiveProofs
 ( MatchContext
 , Match(..), Matches
 , LiveProof(..)
 , conjThName__, conjThName_, conjName__, conjName_
 , conjecture__, conjecture_, conjSC__, conjSC_
 , strategy__, strategy_, mtchCtxts__, mtchCtxts_, focus__, focus_
 , fPath__, fPath_, matches__, matches_, stepsSoFar__, stepsSoFar_
 , LiveProofs
 , writeLiveProofs, readLiveProofs
 , dispLiveProof
 , startProof, launchProof
 , displayMatches
 , buildMatchContext, matchInContexts,matchLawByName, tryLawByName
 , proofIsComplete, finaliseProof
 , undoCalcStep
 , makeEquivalence
 , showLiveProofs
 , showContextLaws
 ) where

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Utilities
import WriteRead
import LexBase
import AST
import SideCond
import TermZipper
import VarData
import Binding
import Matching
import Instantiate
import Laws
import Proofs
import Theories
import Sequents

import NiceSymbols
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\newpage
\subsection{Matching Contexts}

Consider a collection of theories in an ordered list,
where each theory appears in that list before any of those on which
it depends.
Matching a conjecture component against all of these laws
means working through the theories, from first to last.
When working with a given theory, we want to match against
all the laws in that theory, using every variable-data table
in that theory and its dependencies.
In particular, if a pattern variable occurs in more than one var-table,
then we want the data from the first such table.

So given that we are matching in the context of a list of dependency-ordered
theories, we want to use a corresponding list of match contexts,
one for each theory.
A match context for a theory contains all the laws of that theory,
along with a dependency-ordered list of the var-tables,
including that of the theory itself,
as well as those from all subsequent theories.
\begin{code}
type MatchContext
  = ( String       -- Theory Name
    , [Law]        -- all laws of this theory
    , [VarTable] ) -- all known variables here, and in dependencies
\end{code}

Given a list of theories, we generate a list of match-contexts:
\begin{code}
buildMatchContext :: [Theory] -> [MatchContext]
buildMatchContext [] = []
buildMatchContext [thy] = [ (thName thy, laws thy, [known thy]) ]
buildMatchContext (thy:thys) -- thys not null
  = let mcs'@((_,_,vts'):_) = buildMatchContext thys
    in (thName thy, laws thy, known thy : vts') : mcs'
\end{code}

\subsection{Matches}

\begin{code}
data Match
 = MT { mName  ::  String     -- assertion name
      , mAsn   ::  Assertion  -- matched assertion
      , mClass ::  MatchClass -- match class
      , mBind  ::  Binding    -- resulting binding
      , mLocSC ::  SideCond   -- goal side-condition local update
      , mLawSC ::  SideCond   -- law side-condition mapped to goal
      , mRepl  ::  Term       -- replacement term
      } deriving (Eq,Show,Read)

type Matches = [Match]
\end{code}

\newpage
\subsection{Live Proof Type}

\begin{code}
data LiveProof
  = LP {
      conjThName :: String -- conjecture theory name
    , conjName :: String -- conjecture name
    , conjecture :: Assertion -- assertion being proven
    , conjSC :: SideCond -- side condition
    , strategy :: String -- strategy
    , mtchCtxts :: [MatchContext] -- current matching contexts
    , focus :: SeqZip  -- current sub-term of interest
    , fPath :: [Int] -- current term zipper descent arguments
    , matches :: Matches -- current matches
    , stepsSoFar :: [CalcStep]  -- calculation steps so far, most recent first
    }
  deriving (Eq, Show, Read)

conjThName__ f lp = lp{ conjThName = f $ conjThName lp}
conjThName_ = conjThName__ . const
conjName__ f lp = lp{ conjName = f $ conjName lp}
conjName_ = conjName__ . const
conjecture__ f lp = lp{ conjecture = f $ conjecture lp}
conjecture_ = conjecture__ . const
conjSC__ f lp = lp{ conjSC = f $ conjSC lp}
conjSC_ = conjSC__ . const
strategy__ f lp = lp{ strategy = f $ strategy lp}
strategy_ = strategy__ . const
mtchCtxts__ f lp = lp{ mtchCtxts = f $ mtchCtxts lp}
mtchCtxts_ = mtchCtxts__ . const
focus__ f lp = lp{ focus = f $ focus lp}
focus_ = focus__ . const
fPath__ f lp = lp{ fPath = f $ fPath lp}
fPath_ = fPath__ . const
matches__ f lp = lp{ matches = f $ matches lp}
matches_ = matches__ . const
stepsSoFar__ f lp = lp{ stepsSoFar = f $ stepsSoFar lp}
stepsSoFar_ = stepsSoFar__ . const
\end{code}

\subsection{Live Proof Collection}

We maintain a collection of \texttt{LiveProof}s
as a map from theory and conjecture names to the corresponding live proof:
\begin{code}
type LiveProofs = Map (String,String) LiveProof
\end{code}

\newpage
\subsection{Live-Proof Write and Read}

There are two components we don't explicitly save:
\texttt{mtchCtxts},
and
\texttt{matches}.
The first will be re-constructed at read-time,
while the second is simply restored as empty.

\begin{code}
liveproof = "LIVE-PROOF"
lprfHDR = "BEGIN "++liveproof ; lprfTRL ="END "++liveproof
lpthKEY thnm = "TH-NAME: " ++ thnm
lpcjKEY cjnm = "CJ-NAME: " ++ cjnm

conjKEY = "CONJ = "
cjscKEY = "SIDE = "
strtKey st = "STRAT " ++ st
focusKEY = "FOCUS = "
fpathKEY = "FPATH: "
stepsKEY = "STEPS"

writeLiveProof :: LiveProof -> [String]
writeLiveProof lp
  = [ lprfHDR
    , lpthKEY (conjThName lp)
    , lpcjKEY (conjName lp)
    , conjKEY ++ show (conjecture lp)
    , cjscKEY ++ show (conjSC lp)
    , strtKey (strategy lp) ] ++
    -- match contexts not saved
    writeSeqZip (focus lp) ++
    [ fpathKEY ++ show (fPath lp) ] ++
    -- matches not saved
    writePerLine stepsKEY show (stepsSoFar lp) ++
    [ lprfTRL ]

readLiveProof :: Monad m => [Theory] -> [String] -> m (LiveProof,[String])
readLiveProof thylist txts
  = do rest1          <- readThis lprfHDR          txts
       (thnm, rest2)  <- readKey (lpthKEY "") id   rest1
       (cjnm, rest3)  <- readKey (lpcjKEY "") id   rest2
       (conj, rest4)  <- readKey conjKEY read      rest3
       (sc,   rest5)  <- readKey cjscKEY read      rest4
       (strt, rest6)  <- readKey (strtKey "") id   rest5
       let mctxts = buildMatchContext thylist
       (fcs,  rest7)  <- readSeqZip thylist        rest6
       (fpth, rest8)  <- readKey fpathKEY read     rest7
       (steps, rest9) <- readPerLine stepsKEY read rest8
       rest10         <- readThis lprfTRL          rest9
       return ( LP { conjThName = thnm
                   , conjName = cjnm
                   , conjecture = conj
                   , conjSC = sc
                   , strategy = strt
                   , mtchCtxts = mctxts
                   , focus = fcs
                   , fPath = fpth
                   , matches = []
                   , stepsSoFar = steps }
              , rest10 )
\end{code}



\newpage
\subsection{Writing and Reading Live Proofs}

\begin{code}
liveproofs = "LIVE-PROOFS"
lprfsHDR = "BEGIN "++liveproofs ; lprfsTRL ="END "++liveproofs

lprfsKEY = "LIVEPROOFS = "

writeLiveProofs :: LiveProofs -> [String]
writeLiveProofs liveProofs
  = [ lprfsHDR ] ++
    writeMap liveproofs writeLiveProof liveProofs ++
    [ lprfsTRL ]

readLiveProofs :: Monad m => [Theory] -> [String] -> m (LiveProofs,[String])
readLiveProofs thylist txts
  = do rest1         <- readThis lprfsHDR txts
       (lprfs,rest2) <- readMap liveproofs rdKey (readLiveProof thylist) rest1
       rest3         <- readThis lprfsTRL rest2
       return (lprfs,rest3)
\end{code}


\newpage
\subsection{Proof Starting and Stopping}

\subsubsection{Starting a Proof with default strategy}


We need to setup a proof from a conjecture:
\begin{code}
startProof :: LogicSig -> [Theory] -> String -> String -> Assertion -> LiveProof
startProof logicsig thys thnm cjnm asn@(t,sc)
  =  LP { conjThName = thnm
        , conjName = cjnm
        , conjecture = asn
        , conjSC = sc
        , strategy = strat
        , mtchCtxts =  mcs
        , focus =  sz
        , fPath = []
        , matches = []
        , stepsSoFar = []
        }
  where
    (strat,seq) = fromJust $ reduce logicsig thys (cjnm,asn)
    sz = leftConjFocus seq
    mcs = buildMatchContext thys
\end{code}

\subsubsection{Starting a Proof with given strategy}

\begin{code}
launchProof :: [Theory] -> String -> String -> Assertion -> (String,Sequent)
            -> LiveProof
launchProof thys thnm cjnm asn@(t,sc) (strat,seq)
  = LP { conjThName = thnm
       , conjName = cjnm
       , conjecture = asn
       , conjSC = sc
       , strategy = strat
       , mtchCtxts =  mcs
       , focus =  sz
       , fPath = []
       , matches = []
       , stepsSoFar = []
       }
  where
    sz = leftConjFocus seq
    hthy = hyp seq
    mcs = if null $ laws hthy
           then buildMatchContext thys
           else buildMatchContext (hthy:thys)
\end{code}

\newpage
\subsubsection{Testing for Proof Completion}


We need to determine when a live proof is complete:
\begin{code}
proofIsComplete :: LogicSig -> LiveProof -> Bool
proofIsComplete logicsig liveProof
  =  let
       sequent = exitSeqZipper $ focus liveProof
       hypTerms = map (fst . snd . fst) $ laws $ hyp sequent
     in cleft sequent == cright sequent -- should be alpha-equivalent
        ||
        any (== theFalse logicsig) hypTerms
\end{code}

\subsubsection{Finalising a complete Proof}

We need to convert a complete live proof to a proof:
\begin{code}
finaliseProof :: LiveProof -> Proof
finaliseProof liveProof
  = ( conjName liveProof
    , conjecture liveProof
    , strategy liveProof
    , ( exitTZ $ fst $ focus liveProof
      , reverse $ stepsSoFar liveProof ) )
\end{code}

\newpage
\subsection{Trying a Match}

Sometimes we want to see what happens when we single out a law,
including observing any match failure messages.
Here we painstakingly check every monadic call from \texttt{match} onwards,
and report the outcome.
These calls are:
  \texttt{match}%
, \texttt{completeBind}%
, \texttt{instantiateSC}%
, and \texttt{scDischarged}.
\begin{code}
tryLawByName :: LogicSig -> Assertion -> String -> [Int] -> [MatchContext]
               -> YesBut ( Binding    -- mapping from pattern to candidate
                         , Term       -- autoInstantiated Law
                         , SideCond ) -- updated candidate side-condition
tryLawByName logicsig asn@(tC,scC) lnm parts mcs
  = do (((_,(tP,scP)),_),vts) <- findLaw lnm mcs
       partsP <- findParts parts tP
       tryMatch vts tP partsP scP
  where
\end{code}

First, try the structural match.
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    tryMatch vts tP partsP scP
      = case match vts tC partsP of
          -- Yes bind  ->  tryCompleteBinding vts tP partsP scP bind
          Yes bind  ->  tryAutoInstantiate vts tP partsP scP bind
          But msgs
           -> But ([ "try match failed"
                   , ""
                   , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , ""
                   ]++msgs)
\end{code}

At this point we have matched the candidate against part of the law,
with the rest of the law to be the ``replacement''.
However, the replacement may contain variables not present in the
matched part.
We need to find appropriate bindings for these,
keeping the pattern side-conditions in mind.
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    tryAutoInstantiate vts tP partsP scP bind
      = let
          unbound = findUnboundVars (pdbg "bind" bind) $ pdbg "tP" tP
          lvps = termLVarPairings tP
          sEqv = mkEquivClasses lvps
          qbind = questionableBinding bind sEqv $ pdbg "unbound" unbound
          abind = mergeBindings bind $ pdbg "qbind" qbind
        in case instantiate (pdbg "abind" abind) tP of
            Yes tPasC ->  tryInstantiateSC abind scC tPasC partsP scP
            But msgs
             -> But ([ "auto-instantiate failed"
                     , ""
                     , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                     , ""
                     , "lnm[parts]="++lnm++show parts
                     , "tP="++trTerm 0 tP
                     , "partsP="++trTerm 0 partsP
                     , "tC="++trTerm 0 tC
                     , "scC="++trSideCond scC
                     , ""
                     , "bind  = " ++ trBinding bind
                     , "unbound = " ++ trVSet unbound
                     , "qbind = " ++ trBinding qbind
                     , "abind = " ++ trBinding abind
                     ]++msgs)
\end{code}

At this point we have matched the candidate against part of the law,
with the rest of the law to be the ``replacement''.
However, the replacement may contain variables not present in the
matched part.
We need to find appropriate bindings for these,
keeping the pattern side-conditions in mind.
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    tryCompleteBinding vts tP partsP scP bind
      = case completeBind vts tC scC tP scP bind of
          Yes (bind',scC',scP')  ->  tryInstantiateSC bind' scC' tP partsP scP'
          But msgs
           -> But ([ "try complete binding failed"
                   , ""
                   , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , ""
                   ]++msgs)
\end{code}

\newpage
Next, instantiate the pattern side-condition using the bindings.
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    tryInstantiateSC bind scC' tP partsP scP
      = case instantiateSC bind scP of
          Yes scP'  ->  trySCDischarge bind tP partsP scC' scP'
          But msgs
           -> But ([ "try s.c. instantiation failed"
                   , ""
                   , trBinding bind ++ "("++trSideCond scP++")"
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "scP="++trSideCond scP
                   , ""
                   ]++msgs)
\end{code}

Finally, try to discharge the instantiated side-condition:
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    trySCDischarge bind tP partsP scC' scP'
      = do  if scDischarged scC' scP'
              then Yes (bind,tP,scC')
              else But [ "try s.c. discharge failed"
                       , ""
                       , trSideCond scC
                         ++ " " ++ _implies ++ " " ++
                         trSideCond scP'
                       , ""
                       , "lnm[parts]="++lnm++show parts
                       , "tC="++trTerm 0 tC
                       , "scC="++trSideCond scC
                       , "tP="++trTerm 0 tP
                       , "partsP="++trTerm 0 partsP
                       , "scP'="++trSideCond scP'
                       , "bind:\n"
                       , trBinding bind
                       ]
\end{code}

Done.
\begin{code}
-- end tryLawByName
\end{code}

\newpage
\subsubsection{Finding parts of laws}

Looking up a law by name:
\begin{code}
findLaw :: Monad m => String -> [MatchContext] -> m (Law,[VarTable])
findLaw lnm [] = fail ("Law '"++lnm++"' not found")
findLaw lnm ((thnm,lws,vts):mcs)
 = case filter (\law -> lawName law == lnm) lws of
     []       ->  findLaw lnm mcs
     (law:_)  ->  return (law,vts)
\end{code}

Finding `parts' of a top-level constructor:
\begin{code}
findParts :: Monad m => [Int] -> Term -> m Term
findParts [] t = return t
findParts parts (Cons tk n ts)
  = do ts' <- getParts (filter (>0) parts) ts
       case ts' of
         [t']  ->  return t'
         _     ->  return $ Cons tk n ts'
findParts parts t
          = fail ("findParts: "++trTerm 0 t++" "++show parts++" makes no sense")
\end{code}

Assume all \texttt{Int}s are positive and non-zero
\begin{code}
getParts :: Monad m => [Int] -> [a] -> m [a]
getParts [] xs = fail "getParts: no parts specified"
getParts (p:_) [] = fail ("getParts: no parts from "++show p++" onwards")
getParts [p] xs
 | p <= length xs  = return [xs!!(p-1)]
 | otherwise = fail ("getParts: no such part number "++show p)
getParts (p:ps) xs
 | p <= length xs  = do xps <- getParts ps xs
                        return ((xs!!(p-1)) : xps)
 | otherwise = fail ("getParts: no such part number "++show p)
\end{code}


\newpage
\subsection{Completing a Binding}

We have $t_C, sc_C, t_P, sc_P, t_{part}$
and $\beta$ from matching $t_C :: t_{part}$,
as well as the ``known'' variables $\kappa$.
Here we need to:
\begin{enumerate}
  \item
    Determine variables mentioned in the law that have not been matched ($vs_{um}$),
    because they occur outside the matched part.
    $$ vs_{um} = varsIn(t_P) \setminus \dom(\beta)$$
  \item
    Remove any that are ``known'' (perhaps bind to self?)
    $$vs_{ukm} = vs_{um} \setminus \dom(\kappa)$$
  \item
    Identify the law ASCs ($sc_{umP}$) that refer to the remaining
    unmatched variables.
    $$sc_{umP} = sc_P \cap vs_{ukm}$$
  \item
    For any $asc = \exists\lst x \supseteq P$ in $sc_{umP}$ :
    \begin{enumerate}
      \item $asc := \lst x \supseteq P$
      \item $sc_C := sc_C \land \lst x \subseteq \beta(P) $
      \item Possibly bind $\lst x$ to itself?
    \end{enumerate}
  \item
    Not sure what to do about other ASCs in $sc_{umP}$ just now.
\end{enumerate}
\textbf{
  In fact all pattern \texttt{ExCover} should be converted to \texttt{Covers},
  but only once the above steps have been done.
}

\begin{code}
completeBind :: Monad m
             => [VarTable] -> Term -> SideCond -> Term -> SideCond
             -> Binding -> m (Binding,SideCond,SideCond)
completeBind vts tC scC tP scP bind
  | S.null unMappedUnkVars  =  return (bind,scC,scP)
  | otherwise  = completeASCs vts tC scC tP bind mappedASCs unMappedASCs
  where
    unMappedVars = mentionedVars tP S.\\ mappedVars bind
    unMappedUnkVars = S.filter (isUnknownGVar vts) unMappedVars
    unMappedASCs = citingASCs unMappedUnkVars scP
    mappedASCs = scP \\ unMappedASCs

completeASCs :: Monad m
             => [VarTable] -> Term -> SideCond -> Term -> Binding
             -> SideCond -> SideCond -> m (Binding,SideCond,SideCond)
completeASCs vts tC scC tP bind mascP [] = return (bind,scC,mascP)
completeASCs vts tC scC tP bind mascP (ExCover gv vs:unMappedASCs)
  = do scE <- instantiateASC bind (Covers gv vs)
       scC' <- mrgSideCond scC scE
       mascP' <- mrgAtmCond (Covers gv vs) mascP
       completeASCs vts tC scC' tP bind mascP' unMappedASCs
completeASCs vts tC scC tP bind mascP (umSC:unMappedASCs)
  = fail ("completeBind: not yet handling unmapped: " ++ trSideCond [umSC] )
\end{code}

\newpage
\subsection{Matching in Context}

First, given list of match-contexts, systematically work through them.
\begin{code}
matchInContexts :: LogicSig -> [MatchContext] -> Assertion -> Matches
matchInContexts logicsig mcs asn
  = concat $ map (matchLaws logicsig asn) mcs
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: LogicSig -> Assertion -> MatchContext -> Matches
matchLaws logicsig asn (_,lws,vts) = concat $ map (domatch logicsig vts asn) lws
\end{code}

Sometimes we are interested in a specific (named) law.
\begin{code}
matchLawByName :: Monad m => LogicSig -> Assertion -> String -> [MatchContext]
               -> m Matches
matchLawByName logicsig asn lnm mcs
 = do (law,vts) <- findLaw lnm mcs
      return $ domatch logicsig vts asn law
\end{code}

For each law,
we match the whole thing,
and if its top-level is a \texttt{Cons}
with at least two sub-components, we try all possible partial matches.
\begin{code}
domatch :: LogicSig -> [VarTable] -> Assertion -> Law -> Matches
domatch logicsig vts asnC law@((_,(tP@(Cons _ i tsP@(_:_:_)),_)),_)
  =    basicMatch MatchAll vts law (theTrue logicsig) asnC tP
    ++ doPartialMatch i logicsig vts law asnC tsP
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch logicsig vts asnC law@((_,(tP,_)),_)
  =  basicMatch MatchAll vts law (theTrue logicsig) asnC tP
\end{code}


\newpage
\subsection{Assertion Matching}

\subsubsection{Partial Matching}

Here we have a top-level \texttt{Cons}
with at least two sub-terms.
\begin{code}
doPartialMatch :: Identifier -> LogicSig -> [VarTable]
               -> Law -> Assertion -> [Term]
               -> Matches
\end{code}

First, if we have $\equiv$ we call an $n$-way equivalence matcher:
\begin{code}
doPartialMatch i logicsig vts law asnC tsP
  | i == theEqv logicsig  =  doEqvMatch logicsig vts law asnC tsP
\end{code}

If we have $\implies$, then we can try to match either side.
We rely here on the following law of implication:
\begin{eqnarray*}
  P \land Q \equiv P & = \quad P \implies Q \quad = & P \lor Q \equiv Q
\end{eqnarray*}
This means that if we match candidate $C$ against $P$ in law $P\implies Q$
with binding $\beta$,
then we can replace $C$ by $P\beta \land Q\beta$.
If we match $Q$, we can replace $C$ by $Q\beta \lor P\beta$
\begin{code}
doPartialMatch i logicsig vts law asnC tsP@[ltP,rtP]
  | i == theImp logicsig
    =    basicMatch MatchAnte vts law (Cons P land [ltP,rtP]) asnC ltP
      ++ basicMatch MatchCnsq vts law (Cons P lor  [rtP,ltP]) asnC rtP
  where
     land = theAnd logicsig
     lor  = theOr  logicsig
\end{code}

Anything else won't match (right now we don't support $\impliedby$).
\begin{code}
doPartialMatch i logicsig vts law asnC tsP
  = fail ("doPartialMatch `"++trId i++"`, too many sub-terms")
\end{code}

\newpage
\subsubsection{Equivalence Partial Matching}

Do an n-way equivalence match, where we want to match against all possibilities,
exploiting the associative nature of $\equiv$,
as described in \cite[p29]{gries.93}.
First we give shorthand notation for n-ary uses of $\equiv$
and interesting subsets.
\begin{eqnarray*}
   \mathop\equiv_i(p_1^n) &=& p_1 \equiv p_2 \equiv \dots \equiv p_n,
   \qquad i = 1 \dots n \land n > 1
\\ \mathop\equiv_i(p_1^n)\setminus \setof j
   &=&
   p_1 \equiv \dots \equiv p_{j-1}  \equiv p_{j+1} \equiv \dots \equiv p_n
\\ \mathop\equiv_i(p_1^n) |_{\setof{a,\dots,z}}
   &=&
   p_a \equiv \dots \equiv p_z,
   \quad \setof{a,\dots,z} \subseteq \setof{1\dots n}
\end{eqnarray*}
$$
\begin{array}{|l|c|c|c|c|}
\hline
   \textrm{Case}
 & \textrm{Cand.($c$)} & \textrm{Patn.} & \textrm{Match.} & \textrm{Repl.}
\\\hline
   A.
 & \textrm{any } c
 & P \equiv P
 & c :: (P \equiv P) \textrm{ (only!)}
 & \true
\\\hline
   B.
 & \textrm{any } c
 & \mathop\equiv_i(p_1^n)
 & c :: p_j
 & \mathop\equiv_i(p_i^n)\setminus j
\\\hline
   C.
 & \mathop\equiv_j(c_1^m), m \leq n
 & \mathop\equiv_i(p_1^n)
 & c_j :: p_i, i \in J, \#J = m, J \subseteq \setof{1\dots n}
 & \mathop\equiv_i(p_1^n)\setminus J
\\\hline
\end{array}
$$
Case A prevents spurious matches of \QNAME{$\equiv$-refl}
where we match $c::P$ with replacment $P$ to obtain result $c$.
We fully support Cases A and B and give some support to Case C.

First, Case A, which is automatically done above by \texttt{basicMatch},
so we need not return any matches here.
\begin{code}
doEqvMatch :: LogicSig -> [VarTable] -> Law -> Assertion
           -> [Term]    -- top-level equivalence components in law
           -> Matches
-- rule out matches against one-side of the reflexivity axiom
doEqvMatch _ _ _ _ [tP1,tP2] | tP1 == tP2  =  []
\end{code}
Then invoke Cases C and B, in that order.
\begin{code}
doEqvMatch logicsig vts law asnC tsP
  = doEqvMatchC logicsig vts law asnC tsP
    ++
    doEqvMatchB logicsig vts law asnC [] [] tsP
\end{code}

Next, Case B.
\begin{code}
doEqvMatchB logicsig vts law asnC mtchs _ [] = mtchs
doEqvMatchB logicsig vts law@((_,(_,scP)),_) asnC mtchs sPt (tP:tPs)
  = let mtchs' = basicMatch (MatchEqv [length sPt + 1])
                     vts law (eqv (reverse sPt ++ tPs)) asnC tP
    in doEqvMatchB logicsig vts law asnC (mtchs'++mtchs) (tP:sPt) tPs
  where
    eqv []   =  theTrue logicsig
    eqv [t]  =  t
    eqv ts   =  Cons P (theEqv logicsig) ts
\end{code}

\newpage
Case C only applies if the \emph{candidate} is an equivalence.
We will assume $m < n$ and just try $J$ being either
the first $m$ pattern components ($\setof{1\dots m}$),
or the last $m$ (\setof{n+1-m\dots n}).
\begin{code}
-- doEqvMatchC logicsig vts law asnC tsP
doEqvMatchC :: LogicSig -> [VarTable] -> Law -> Assertion ->[Term]
            -> Matches
doEqvMatchC logicsig vts law@((_,(_,scP)),_) asnC@(tC@(Cons tk i tsC),scC) tsP
 | i == theEqv logicsig
   && cLen < pLen  = doEqvMatchC' cLen [1..cLen]
                       logicsig vts law scC tsC tsP
                     ++
                     doEqvMatchC' cLen [pLen+1-cLen .. pLen]
                       logicsig vts law scC (reverse tsC) (reverse tsP)
 where
    cLen = length tsC
    pLen = length tsP
doEqvMatchC _ _ _ _ _ = []

-- we assume cLen < pLen here
doEqvMatchC' :: Int -> [Int] -> LogicSig -> [VarTable] -> Law
             -> SideCond -> [Term] -> [Term]
             -> Matches
doEqvMatchC' cLen is logicsig vts law@((_,(_,scP)),_) scC tsC tsP
  = basicMatch (MatchEqv is) vts law (eqv tsP'') (eqv tsC,scC) (eqv tsP')
  where
    (tsP',tsP'') = splitAt cLen tsP
    eqv []   =  theTrue logicsig
    eqv [t]  =  t
    eqv ts   =  Cons P (theEqv logicsig) ts
\end{code}


\newpage
\subsubsection{Just Match it, dammit!}

\textbf{
Instantiation needs to be more nuanced.
Here we should take pattern variables in the replacement,
but not in the binding (because they were not in the pattern),
and map them to their own name with a question mark added.
We should have a \texttt{matchInstantiate}
that does \texttt{findUnbound},
generates the ``?'' bindings for those,
and then does \texttt{instantiate}.
}


Do a basic match,
including side-condition checking.
\begin{code}
basicMatch :: MatchClass
            -> [VarTable] -- known variables in scope at this law
            -> Law        -- law of interest
            -> Term       -- sub-part of law not being matched
            -> Assertion  -- candidate assertion
            -> Term       -- sub-part of law being matched
            -> Matches
basicMatch mc vts law@((n,asn@(tP,scP)),_) repl asnC@(tC,scC) partsP
  =  do bind <- match vts tC partsP
        (bind',scC',scP') <- completeBind vts tC scC tP scP bind
        scP'' <- instantiateSC bind' scP'
        if scDischarged scC' scP''
         then
           [MT n asn (chkPatn mc tP) bind' scC' scP'' repl
           -- (autoInstantiate bind' repl)
           ]
          -- case instantiate bind' repl of
          --   Nothing     ->  []
          --   Just irepl  ->  [MT n asn (chkPatn mc tP) bind' scC' scP'' irepl]
        else []
  where

    chkPatn mc (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  trivialise mc
    chkPatn mc _                             =  mc

    trivialise (MatchEqv [i])  =  MatchEqvVar i
    trivialise mc              =  mc
\end{code}

\newpage
\subsubsection{Undoing a Proof Step}

\textbf{
 We would like to restore focus when backing up a simple step,
 such as UseLaw.
}
\begin{code}
undoCalcStep :: LiveProof -> LiveProof
undoCalcStep liveProof
  = case stepsSoFar liveProof of
      []                       ->  liveProof
      ((just,(term,sc)):prevSteps)
        ->  matches_ []
            $ fPath_ []
            $ conjSC_ sc
            $ stepsSoFar_ prevSteps
            $ focus__ (setTerm term)
            $ undoCalcStep' just
  where

    undoCalcStep' (Switch CLeft _)
       =  focus__ ( leftConjFocus  . exitSeqZipper ) liveProof
    undoCalcStep' (Switch CRight _)
       =  focus__ ( rightConjFocus . exitSeqZipper ) liveProof
    undoCalcStep' (Switch (Hyp i) _)
       =  focus__ ( fromJust . -- this should always succeed !
                    hypConjFocus i . exitSeqZipper) liveProof

    -- THIS IS WRONG as we set stepsSoFar to prevSteps after doing this!
    undoCalcStep' _  = liveProof

    setTerm t (tz,seq') = (mkTZ t,seq')
\end{code}


\newpage
\subsection{Making a Theorem}

Given an incomplete ``reduce all to true'' proof attempt of $P_0$
that has done a straight calculation as far as $P_n$,
produce a complete ``reduce left to right'' proof
of $P_0 \equiv P_n$.

\begin{code}
makeEquivalence :: String -> LiveProof
                -> ( String -- name of theory to contain new law
                   , Law    -- the new law
                   , Proof ) -- the relevant proof
makeEquivalence nm liveProof
  = (  conjThName liveProof
    , ( ( nm, asn ), Proven nm )
    , ( nm, asn, strategy liveProof, calc )
    )
  where
     -- hack - should refer to logicSig
     equiv = fromJust $ ident "equiv"
     mkEquivs ps = PCons equiv ps
     p === q = mkEquivs [p,q]
     step0 = fst $ conjecture liveProof
     step' = exitTZ $ fst $ focus liveProof
     sc = conjSC liveProof
     asn = ( step0 === step', sc)
     calc = ( step' , reverse $ stepsSoFar liveProof )
\end{code}

\newpage
\subsection{Showing Live Proofs}

\textbf{This should all be done via proper generic rendering code}


Showing Proof:
\begin{code}
showLiveProofs :: LiveProofs -> String
showLiveProofs lproofs
 | M.null lproofs  =  "No ongoing (live) proofs."
 | otherwise       =  unlines' [ "Current live (incomplete) proofs:"
                               , numberList showLiveProof $ M.elems lproofs ]

showLiveProof :: LiveProof -> String
showLiveProof liveProof
  =  conjThName liveProof
     ++ "." ++ conjName liveProof
     ++ " [" ++ strategy liveProof ++ "]"
     ++ " @ " ++ dispSeqTermZip (focus liveProof)
\end{code}

\begin{code}
-- displays whole proof in proof REPL
-- temporary
dispLiveProof :: LiveProof -> String
dispLiveProof liveProof
 = unlines
     ( ( ("Proof for "++red (widthHack 2 $ conjName liveProof))
       : ("\t" ++ green(trTerm 0 trm ++ "  "++ trSideCond sc))
       : ("by "++strategy liveProof)
       : map shLiveStep (reverse (stepsSoFar liveProof))
       )
       ++
       ( " ..."
         : displayMatches (matches liveProof)
         : [ underline "           "
           , dispSeqZip (fPath liveProof) (conjSC liveProof) (focus liveProof)
           , "" ]
       ) )
 where (trm,sc) = conjecture liveProof

shLiveStep :: CalcStep -> String
shLiveStep ( just, asn )
  = unlines' [ trAsn asn
             , showJustification just]

displayMatches :: Matches -> String
displayMatches []  =  ""
displayMatches matches
  =  unlines' ( ("Matches:") : map shMatch (zip [1..] matches))

shMatch (i, mtch)
 = show i ++ " : "++ ldq ++ green (nicelawname $ mName mtch) ++ rdq
   ++ "  gives  "
   ++ (bold $ blue $ trTerm 0 $ pdbg "brepl" $ brepl)
   ++ "  " ++ shSCImplication (mLocSC mtch) (mLawSC mtch)
   ++ " " ++ shMClass (mClass mtch)
 where
    bind = mBind mtch
    brepl = autoInstantiate bind $ mRepl mtch
    (_,lsc) = mAsn mtch

shSCImplication scC scPm
  =     trSideCond scC
     ++ " " ++ _implies ++ " "
     ++ trSideCond scPm

shMappedCond bind lsc
  = case instantiateSC bind lsc of
      Nothing    ->  trSideCond lsc ++ (red " (law-sc!)")
      Just ilsc  ->  trSideCond ilsc

shMClass MatchAll         =  green "*"
shMClass (MatchEqv is)    =  green (_equiv++show is)
shMClass MatchAnte        =  green ("*"++_implies)
shMClass MatchCnsq        =  green (_implies++"*")
shMClass (MatchEqvVar i)  =  red "trivial!"
\end{code}

We can display laws from a context (again, this should be done elsewhere).
\begin{code}
showContextLaws (nm,lws,_)
  = unlines' (
      [ "Theory '"++nm++"'"
      , showLaws lws
      ] )
\end{code}
