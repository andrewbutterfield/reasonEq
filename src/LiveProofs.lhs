\chapter{Live Proof Support}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LiveProofs
 ( LiveProof(..)
 , conjThName__, conjThName_, conjName__, conjName_
 , conjecture__, conjecture_, conjSC__, conjSC_
 , strategy__, strategy_, mtchCtxts__, mtchCtxts_
 , liveSettings__, liveSettings_
 , focus__, focus_
 , fPath__, fPath_, matches__, matches_, stepsSoFar__, stepsSoFar_
 , xpndSC__, xpndSC_
 , LiveProofs
 , renderLiveProofs, parseLiveProofs
 , dispLiveProof
 , dispEndProof
 , launchProof
 , displayMatches
 -- , instantiateRepl, instReplInMatch
 , matchInContexts, matchLawByName, tryLawByName
 , proofIsComplete, finaliseProof
 , undoCalcStep
 , makeEquivalence
 , showLiveProofs
 , showContextLaws
 , showContextKnowns
 ) where

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import YesBut 
import Utilities
import WriteRead
import LexBase
import Variables
import Types
import AST
import SideCond
import Assertions
import TermZipper
import VarData
import Binding
import Matching
import AlphaEquiv
import Instantiate
import Laws
import Proofs
import Theories
import Sequents
import MatchContext
import Typing
import ProofMatch
import ProofSettings

import Symbols
import TestRendering

import StdTypeSignature
import StdSignature

import Debugger
\end{code}

\newpage
\section{Live  Type}

\begin{code}
data LiveProof
  = LP {
      conjThName :: String -- conjecture theory name
    , conjName :: String -- conjecture name
    , conjecture :: Assertion -- assertion being proven
    , conjSC :: SideCond -- side condition
    , strategy :: String -- strategy
    , mtchCtxts :: [MatchContext] -- current matching contexts
    , liveSettings :: ProofSettings
    , focus :: SeqZip  -- current sub-term of interest
    , fPath :: [Int] -- current term zipper descent arguments
    , matches :: Matches -- current matches
    , stepsSoFar :: [CalcStep]  -- calc steps so far, most recent first
    -- derived fron conjSC, using mtchCtxts
    , xpndSC :: SideCond -- side condition with known vars expanded
    }
  -- deriving (Eq, Show, Read)

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
liveSettings__ f lp = lp{ liveSettings = f $ liveSettings lp}
liveSettings_ = liveSettings__ . const
focus__ f lp = lp{ focus = f $ focus lp}
focus_ = focus__ . const
fPath__ f lp = lp{ fPath = f $ fPath lp}
fPath_ = fPath__ . const
matches__ f lp = lp{ matches = f $ matches lp}
matches_ = matches__ . const
stepsSoFar__ f lp = lp{ stepsSoFar = f $ stepsSoFar lp}
stepsSoFar_ = stepsSoFar__ . const
xpndSC__ f lp = lp{ xpndSC = f $ xpndSC lp}
xpndSC_ = xpndSC__ . const
\end{code}

\section{Live Proof Collection}

We maintain a collection of \texttt{LiveProof}s
as a map from theory and conjecture names to the corresponding live proof:
\begin{code}
type LiveProofs = Map (String,String) LiveProof
\end{code}

\newpage
\section{Live-Proof Write and Read}

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

renderLiveProof :: LiveProof -> [String]
renderLiveProof lp
  = [ lprfHDR
    , lpthKEY (conjThName lp)
    , lpcjKEY (conjName lp)
    , conjKEY ++ show (conjecture lp)
    , cjscKEY ++ show (conjSC lp)
    , strtKey (strategy lp) ] ++
    -- match contexts not saved
    renderProofSettings (liveSettings lp) ++
    writeSeqZip (focus lp) ++
    [ fpathKEY ++ show (fPath lp) ] ++
    -- matches not saved
    writePerLine stepsKEY show (stepsSoFar lp) ++
    [ lprfTRL ]
    -- xpndSC not saved

parseLiveProof :: MonadFail m => TheoryDAG -> [String] -> m (LiveProof,[String])
parseLiveProof thrys txts
  = do rest1          <- readThis lprfHDR          txts
       (thnm, rest2)  <- readKey (lpthKEY "") id   rest1
       (cjnm, rest3)  <- readKey (lpcjKEY "") id   rest2
       (conj, rest4)  <- readKey conjKEY read      rest3
       (sc,   rest5)  <- readKey cjscKEY read      rest4
       (strt, rest6)  <- readKey (strtKey "") id   rest5
       let thylist = fromJust $ getTheoryDeps thnm thrys
       let mctxts = buildMatchContext thylist
       (pset,rest7) <- parseProofSettings          rest6
       (fcs,  rest8)  <- readSeqZip thylist        rest7
       (fpth, rest9)  <- readKey fpathKEY read     rest8
       (steps, rest10) <- readPerLine stepsKEY read rest9
       rest11         <- readThis lprfTRL          rest10
       return ( LP { conjThName = thnm
                   , conjName = cjnm
                   , conjecture = conj
                   , conjSC = sc
                   , strategy = strt
                   , mtchCtxts = mctxts
                   , liveSettings = pset
                   , focus = fcs
                   , fPath = fpth
                   , matches = []
                   , stepsSoFar = steps 
                   , xpndSC = expandSideCondKnownVars mctxts sc }
              , rest11 )
\end{code}



\newpage
\section{Writing and Reading Live Proofs}

\begin{code}
liveproofs = "LIVE-PROOFS"
lprfsHDR = "BEGIN "++liveproofs ; lprfsTRL ="END "++liveproofs

lprfsKEY = "LIVEPROOFS = "

renderLiveProofs :: LiveProofs -> [String]
renderLiveProofs liveProofs
  = [ lprfsHDR ] ++
    writeMap liveproofs renderLiveProof liveProofs ++
    [ lprfsTRL ]

parseLiveProofs :: MonadFail m 
               => TheoryDAG -> [String] -> m (LiveProofs,[String])
parseLiveProofs thrys txts
  = do rest1         <- readThis lprfsHDR txts
       (lprfs,rest2) <- readMap liveproofs rdKey (parseLiveProof thrys) rest1
       rest3         <- readThis lprfsTRL rest2
       return (lprfs,rest3)
\end{code}


\newpage
\section{Proof Starting and Stopping}

\subsection{Starting a Proof with given strategy}

\begin{code}
launchProof :: [Theory] -> String -> String -> Assertion -> (String,Sequent)
            -> LiveProof
launchProof thys thnm cjnm asn@(Assertion t sc) (strat,sequent)
  = LP { conjThName = thnm
       , conjName = cjnm
       , conjecture = asn
       , conjSC = sc
       , strategy = strat
       , mtchCtxts =  mcs
       , liveSettings = initProofSettings
       , focus =  sz
       , fPath = []
       , matches = []
       , stepsSoFar = []
       , xpndSC = expandSideCondKnownVars mcs sc
       }
  where
    sz = leftConjFocus sequent
    hthy = hyp sequent
    mcs = if null $ laws hthy
          then buildMatchContext thys
          else buildMatchContext (hthy:thys)
\end{code}

\newpage
\subsection{Testing for Proof Completion}


We need to determine when a live proof is complete:
\begin{code}
proofIsComplete :: LiveProof -> Bool
proofIsComplete liveProof
  =  let
       sequent = exitSeqZipper $ focus liveProof
       hypTerms = map (assnT . snd . fst) $ laws $ hyp sequent
     in cleft sequent =~= cright sequent
        ||
        any (== theFalse) hypTerms
\end{code}

\subsection{Finalising a complete Proof}

We need to convert a complete live proof to a proof:
\begin{code}
finaliseProof :: LiveProof -> Proof
finaliseProof liveProof
  = ( conjThName liveProof
    , conjName liveProof
    , conjecture liveProof
    , strategy liveProof
    , ( exitTZ $ fst $ focus liveProof
      , reverse $ stepsSoFar liveProof ) )
\end{code}

\newpage
\section{Trying a Match}

Sometimes we want to see what happens when we single out a law,
including observing any match failure messages.
Here we painstakingly check every monadic call from \texttt{match} onwards,
and report the outcome.
These calls are:
  \texttt{match}%
, $<$Complete Binding$>$%
, \texttt{instantiateSC}%
, and \texttt{scDischarge},
where $<$Complete Binding$>$ for matching involves:
\begin{verbatim}
findUnboundVars termLVarPairings mkEquivClasses questionableBinding
mergeBindings instTerm
\end{verbatim}
and $<$Complete Binding$>$ for application involves(?) \texttt{completeBind}.

\begin{code}
tryLawByName :: Assertion -> String -> [Int] -> [MatchContext] -> TypCmp
               -> YesBut ( Binding    -- mapping from pattern to candidate
                         , SideCond   -- Law side-condition
                         , Term       -- autoInstantiated Law
                         , SideCond   -- updated expanded candidate side-cond.
                         , SideCond ) -- discharged(?) law side-condition
tryLawByName (Assertion tC scC) lnm parts mcs fits
  = do (((_,(Assertion tP scP)),_),vts) <- findLaw lnm mcs
       (partsP,replP) <- findParts parts tP
       let scXP = expandSCKnowns vts scP
       (bind,instlaw,expsc,dischsc) <- tryMatch vts fits tP partsP replP scXP
       return (bind,scP,instlaw,expsc,dischsc)
  where
    -- below we try to do:
    -- bind          <- match vts tC partsP
    -- (kbind,tPasC) <- bindKnown vts bind tP
    -- (fbind,_)     <- bindFloating vts kbind tP
    -- tP'           <- instTerm fbind replP
    -- scP'          <- instantiateSC fbind scP of
    -- scP''         <- scDischarge scC scP' of
    -- return (fbind,tP',scP',scP'')
\end{code}

First, try the structural match.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryMatch vts fits tP partsP replP scP
      = case
                match vts fits tC partsP
        of
          Yes bind  ->  tryInstantiateKnown vts tP partsP replP scP bind
          But msgs
           -> But ([ "try match failed"
                   , ""
                   , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "replP="++trTerm 0 replP
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , "---"
                   ]++msgs)
\end{code}

\newpage
At this point the replacement may contain variables not present in the
matched part, so we need to create temporary bindings for these.
First we see if any of these are ``known''.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiateKnown vts tP partsP replP scP bind
      = case
                bindKnown vts bind tP
        of
          Yes kbind  ->  tryInstantiateFloating vts tP partsP replP scP kbind
          But msgs
           -> But ([ "instTerm knowns failed"
                   , ""
                   , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "replP="++trTerm 0 replP
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , ""
                   , "bind  = " ++ trBinding bind
                   ]++msgs)
\end{code}

Anything unbound and not ``known'' is ``floating'',
and we generate names for these that make their floating nature visible.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiateFloating vts tP partsP replP scP kbind
      = case
                bindFloating vts kbind tP
        of
          Yes fbind  ->  tryInstantiate vts
                           (mkInsCtxt vts scC) 
                           fbind tP partsP replP scP
          But msgs
           -> But ([ "instTerm floating failed"
                   , ""
                   , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "replP="++trTerm 0 replP
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , ""
                   , "kbind  = " ++ trBinding kbind
                   ]++msgs)
\end{code}


Next, instantiate the law using the bindings.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiate vts insctxt fbind tP partsP replP scP
      = case
                instTerm insctxt fbind replP
        of
          Yes tP'  
            ->  tryInstantiateSC vts insctxt fbind tP' partsP replP scP
          But msgs
           -> But ([ "try law instantiation failed"
                   , ""
                   , trBinding fbind
                   , "&& "++trSideCond scP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , "replP="++trTerm 0 replP
                   , "scP="++trSideCond scP
                   , ""
                   ]++msgs)
\end{code}
Next, instantiate the pattern side-condition using the bindings.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiateSC vts insctxt fbind tP' partsP replP scP
      = case
                instantiateSC insctxt fbind scP
        of
          Yes scP'  ->  trySCDischarge vts fbind tP' partsP replP scP'
          But msgs
           -> But ([ "try s.c. instantiation failed"
                   , ""
                   , trBinding fbind
                   , "&& "++trSideCond scP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , "tP'="++trTerm 0 tP'
                   , "partsP="++trTerm 0 partsP
                   , "replP="++trTerm 0 replP
                   , "scP="++trSideCond scP
                   , ""
                   ]++msgs)
\end{code}

Finally, try to discharge the instantiated side-condition:
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    trySCDischarge vts fbind tP' partsP replP scP'
      = case
                scDischarge (getDynamicObservables vts) scC scP'
        of
          Yes scP'' -> Yes (fbind,tP',scP',scP'')
          But whynots -> But [ "try s.c. discharge failed"
                             , unlines' whynots
                             , ""
                             , trSideCond scC
                               ++ " " ++ _imp ++ " " ++
                               trSideCond scP'
                             , ""
                             , "lnm[parts]="++lnm++show parts
                             , "tC="++trTerm 0 tC
                             , "scC="++trSideCond scC
                             , "tP'="++trTerm 0 tP'
                             , "partsP="++trTerm 0 partsP
                             , "replP="++trTerm 0 replP
                             , "scP'="++trSideCond scP'
                             , "fbind:\n"
                             , trBinding fbind
                             ]
\end{code}

Done.
\begin{code}
-- end tryLawByName
\end{code}

\newpage
\subsection{Finding parts of laws}

Looking up a law by name.
We always want to return the var data tables for the theory from which
the lookup is made, rather than the theory where the law is found.
\begin{code}
findLaw :: MonadFail m => String -> [MatchContext] -> m (Law,[VarTable])
findLaw lnm mcs@((_,_,vts):_) = findLaw' vts lnm (map snd3 mcs)
findLaw' vts lnm [] = fail ("Law '"++lnm++"' not found")
findLaw' vts  lnm (lws:lwss)
 = case filter (\law -> lawName law == lnm) lws of
     []       ->  findLaw' vts lnm lwss
     (law:_)  ->  return (law,vts)
\end{code}

Finding `parts' of a top-level constructor.
We assume numbers are non-zero, positive, and ordered.
\begin{code}
findParts :: MonadFail m 
          => [Int]  -- we count from 1 upwards
          -> Term  
          -> m ( Term   -- parts found
               , Term ) -- parts leftover (True, if none)
findParts [] t  =  return (t,theTrue)
findParts parts (Cons tk sn n ts)  
  =  let (wanted,leftover) = getParts [] [] 1 parts ts
     in return (foundCons tk sn n wanted,foundCons tk sn n leftover)
findParts parts t
  = fail ("findParts: "++trTerm 0 t++" "++show parts++" makes no sense")
\end{code}

Assume all \texttt{Int}s are positive and non-zero
\begin{code}
getParts :: [a] -> [a] -> Int -> [Int] -> [a] -> ([a],[a])
getParts wanted left _ _  []  =  (reverse wanted, reverse left)
getParts wanted left _ [] xs  =  (reverse wanted, reverse left ++ xs)
getParts wtd lft pos is@(i:is') (x:xs)
  | i == pos   =  getParts (x:wtd) lft pos' is' xs
  | otherwise  =  getParts wtd (x:lft) pos' is  xs
  where pos' = pos+1

foundCons :: Type -> Bool -> Identifier -> [Term] -> Term
foundCons _  _  _ []   =  theTrue
foundCons _  _  _ [t]  =  t
foundCons tk sn n ts   =  Cons tk sn n ts
\end{code}


\newpage
\section{Matching in Context}

First, given list of match-contexts, systematically work through them,
carrying the top-level view of the variable-tables along.
\begin{code}
matchInContexts :: [MatchContext] -> TypCmp -> Assertion -> Matches
matchInContexts mcs@((_,lws,vts):_) fits asn
  = concat $ map (matchLaws vts fits asn) mcs
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: [VarTable] -> TypCmp -> Assertion -> MatchContext -> Matches
matchLaws vts fits asn (_,lws,_)
  = concat $ map (domatch vts fits $ unwrapASN asn) lws
\end{code}

Sometimes we are interested in a specific (named) law.
\begin{code}
matchLawByName :: MonadFail m
               => Assertion -> String -> [MatchContext] -> TypCmp
               -> m Matches
matchLawByName asn lnm mcs fits
 = do (law,vts) <- findLaw lnm mcs
      return $ domatch vts fits (unwrapASN asn) law
\end{code}

For each law,
we match the whole thing,
and if its top-level is a \texttt{Cons}
with at least two sub-components, we try all possible partial matches.
\begin{code}
domatch :: [VarTable] -> TypCmp -> TermSC -> Law -> Matches
domatch vts fits asnC 
        law@((lname,(Assertion tP@(Cons _ _ i tsP@(_:_:_)) scP)),prov)
  =    basicMatch MatchAll vts fits law' theTrue asnC tP
    ++ doPartialMatch i vts fits law' asnC tsP
  where
    xscP = expandSCKnowns vts scP
    law' =(((lname,mkAsn tP xscP)),prov)
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch vts fits asnC law@((lname,(Assertion tP scP)),prov)
  =  basicMatch MatchAll vts fits law' theTrue asnC tP
  where
    xscP = expandSCKnowns vts scP
    law' =(((lname,mkAsn tP xscP)),prov)
\end{code}


\newpage
\section{Assertion Matching}

\subsection{Partial Matching}

Here we have a top-level \texttt{Cons}
with at least two sub-terms.
\begin{code}
doPartialMatch :: Identifier -> [VarTable] -> TypCmp
               -> Law -> TermSC -> [Term]
               -> Matches
\end{code}

First, if we have $\equiv$ we call an $n$-way equivalence matcher:
\begin{code}
doPartialMatch i vts fits law asnC tsP
  | i == theEqv  =   doEqvMatch vts fits law asnC tsP
\end{code}

If we have two sub-terms,
and either $=$ or $\implies$,
then we can try to match either side.
We rely here on the following law of implication:
\begin{eqnarray*}
  P \land Q \equiv P & = \quad P \implies Q \quad = & P \lor Q \equiv Q
\end{eqnarray*}
This means that if we match candidate $C$ against $P$ in law $P\implies Q$
with binding $\beta$,
then we can replace $C$ by $P\beta \land Q\beta$.
If we match $Q$, we can replace $C$ by $Q\beta \lor P\beta$
\begin{code}
doPartialMatch i vts fits law asnC tsP@[ltP,rtP]
  | i == equals
    =    basicMatch MatchEqvLHS vts fits law rtP asnC ltP
      ++ basicMatch MatchEqvRHS vts fits law ltP asnC rtP
  | i == theImp
    =    basicMatch MatchAnte vts fits law 
                    (Cons pred1 True theAnd [ltP,rtP]) asnC ltP
      ++ basicMatch MatchCnsq vts fits law 
                    (Cons pred1 True theOr  [rtP,ltP]) asnC rtP
\end{code}

Anything else won't match (right now we don't support $\impliedby$).
\begin{code}
doPartialMatch i vts fits law asnC tsP
  = fail ("doPartialMatch `"++trId i++"`, too many sub-terms")
\end{code}

\newpage
\subsection{Equivalence Partial Matching}

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

First, Case A is automatically done above by \texttt{basicMatch},
so we need not return any matches here.
\begin{code}
doEqvMatch :: [VarTable] -> TypCmp -> Law -> TermSC
           -> [Term]    -- top-level equivalence components in law
           -> Matches
doEqvMatch vts fits law asnC [tP1,tP2]
-- rule out matches against one-side of the reflexivity axiom
  | tP1 == tP2  =  []
-- otherwise treat binary equivalence specially:
  | otherwise  =     basicMatch MatchEqvLHS vts fits law tP2 asnC tP1
                  ++ basicMatch MatchEqvRHS vts fits law tP1 asnC tP2
\end{code}
Then invoke Cases C and B, in that order.
\begin{code}
doEqvMatch vts fits law asnC tsP
  = doEqvMatchC vts fits law asnC tsP
    ++
    doEqvMatchB vts fits law asnC [] [] tsP
\end{code}

Next, Case B.
\begin{code}
doEqvMatchB vts fits law asnC mtchs _ [] = mtchs
doEqvMatchB vts fits law@((_,(Assertion _ scP)),_) asnC mtchs sPt (tP:tPs)
  = let mtchs' = basicMatch (MatchEqv [length sPt + 1])
                     vts fits law (eqv (reverse sPt ++ tPs)) asnC tP
    in doEqvMatchB vts fits law asnC (mtchs'++mtchs) (tP:sPt) tPs
  where
    eqv []   =  theTrue
    eqv [t]  =  t
    eqv ts   =  Cons pred1 True theEqv ts
\end{code}

\newpage
Case C only applies if the \emph{candidate} is an equivalence.
We will assume $m < n$ and just try $J$ being either
the first $m$ pattern components ($\setof{1\dots m}$),
or the last $m$ (\setof{n+1-m\dots n}).
\begin{code}
-- doEqvMatchC vts law asnC tsP
doEqvMatchC :: [VarTable] -> TypCmp -> Law -> TermSC ->[Term]
            -> Matches
doEqvMatchC vts fits law@((_,(Assertion _ scP)),_)
                         asnC@(tC@(Cons tk si i tsC),scC) tsP
 | i == theEqv
   && cLen < pLen  = doEqvMatchC' cLen [1..cLen]
                       vts fits law scC tsC tsP
                     ++
                     doEqvMatchC' cLen [pLen+1-cLen .. pLen]
                       vts fits law scC (reverse tsC) (reverse tsP)
 where
    cLen = length tsC
    pLen = length tsP
doEqvMatchC _ _ _ _ _ = []

-- we assume cLen < pLen here
doEqvMatchC' :: Int -> [Int] -> [VarTable] -> TypCmp -> Law
             -> SideCond -> [Term] -> [Term]
             -> Matches
doEqvMatchC' cLen is vts fits law@((_,(Assertion _ scP)),_) scC tsC tsP
  = basicMatch (MatchEqv is) vts fits law (eqv tsP'') (eqv tsC,scC) (eqv tsP')
  where
    (tsP',tsP'') = splitAt cLen tsP
    eqv []   =  theTrue 
    eqv [t]  =  t
    eqv ts   =  Cons pred1 True theEqv ts
\end{code}


\newpage
\section{Basic Matching and Application}

An ideal match and apply scenario could be described as follows:
\begin{itemize}
  \item
    We have a goal predicate $G$,
    and we are focussed on sub-predicate $C$,
    we we can write as $G(C)$.
    We also have a side-condition $SCG$.
  \item
    We want to apply law $L$ to $C$,
    where, w.l.o.g., $L$ has the form $P \sim R$,
    by matching $C$ against $P$ to produce a match-binding $\beta$.
  \item
   The law has a side-condition $SCL$ that needs to be discharged.
   We need to show that $SCG \implies \beta(SCL)$.
  \item
   We then apply $\beta$ to $R$ and use that to replace $C$ in $G$.
\end{itemize}
A problem arises when $R$ contains variables not present in $P$.
These will not occur in the binding $\beta$, and we need to figure out what
they should map to. Ideally they should map to replacements that help
discharge the side-condition.
We call this process match-binding \emph{completion}.


The main use of matching is to quickly compare
the focus against \emph{all} the laws in scope,
and display some interesting subset of the successful matches.
We want to display as much of each match as possible using
the variables of the goal and focus, not those of the law.
So we need a form of \emph{auto-completion} that flags
those variables from $R$ that are not in $P$.

One part of this is straightforward.
Any unbound variables from $R \setminus P$ that are ``known''
should be bound to themselves.
The other part, with such variables that are not ``known``,
can be addressed by binding them to a version of themselves
that is marked in some distinguishing way.
We refer to these marked versions as being ``floating'' variables.

\textbf{NOTE: }
\textsl{
 What happens if such a floating $P$ is mentioned in a side-condition?
 Does it come out in the wash as a result of the process detailed just below?
}

When a match is chosen to be applied,
as part of a proof-step,
then the user will be asked to supply instantiations for all variables
bound to floating variables.
The predicates $true$ and $false$, as well as any well-formed sub-component
of the goal can be chosen.

\newpage
\subsection{Match and Auto-Complete}

Given:
\\ --- Goal with focus $G(C)$ and side-condition $SCG$
\\ --- Law $L$ of form $P\sim R$ and side-condition $SCL$

Produce:
\\ --- $P$-match binding $\beta_0$
\\ --- Auto-complete binding $\beta?$
\\ --- Law side-condition in Goal space $SCL?$
\\ --- Side-condition discharge outcome $sc?$

Process:
\begin{eqnarray*}
   \beta_0 &=& match(C::P)
\\ \beta? &=& autocomplete(R,\beta_0)
\\ SCL? &=& \beta?(SCL)
\\ sc? &=& discharge(SCG \implies SCL?)
\end{eqnarray*}

Summary:
\\ $match(G(C),SCG,P,R,SCL) \mapsto (\beta_0,\beta?,SCL?,sc?)$

\includegraphics[scale=0.2]{doc/images/match}

\newpage
\subsection{Goal-Oriented Complete and Build}

Given:
\\ --- Goal with focus $G(C)$ and side-condition $SCG$
\\ --- Law Replacement $R$ and side-condition $SCL$
\\ --- $P$-match binding $\beta_0$

Produce:
\\ --- User-guided complete binding $\beta'$
\\ --- Law side-condition in Goal space $SCL'$
\\ --- Side-condition discharge outcome $sc$
\\ --- Replacement Predicate in Goal space $C'$
\\ --- Goal with updated focus $G(C')$ 
\\ --- Goal side-condition $SCG$ extended with any fresh variables introduced in $sc$.

Process:
\begin{eqnarray*}
   \beta' &=& usercomplete(R,G(C),\beta_0)
\\ SCL' &=& \beta'(SCL)
\\ sc &=& discharge(SCG\implies SCL')
\\ C' &=&\beta'(C)
\\ G(C') &=& G(C)[C'/C]
\\ sc' &=& SCG \cup freshvars(sc)
\end{eqnarray*}

Summary:
\\ $apply(G(C),SCG,R,SCL,\beta_0) \mapsto (\beta',SCL',sc',C',G(C')) $

\includegraphics[scale=0.2]{doc/images/apply}

\newpage
\subsection{Basic Matching}

Do a basic match,
including side-condition checking.
\begin{code}
basicMatch :: MatchClass
            -> [VarTable] -- known variables in scope at this law
            -> TypCmp  -- checks type compatibility 
            -> Law        -- law of interest
            -> Term       -- sub-part of law not being matched
            -> TermSC  -- candidate assertion
            -> Term       -- sub-part of law being matched
            -> Matches
basicMatch mc vts fits 
           law@((n,asnP@(Assertion tP scP)),_) replP 
           (tC,scC) partsP
  =  do bind <- match vts fits tC partsP
        kbind <- bindKnown vts bind tP
        fbind <- bindFloating vts kbind tP -- was replP 
        let insctxt = mkInsCtxt vts scC
        tP' <- instTerm insctxt fbind replP
        scP' <- instantiateSC insctxt fbind scP
        scP'' <- scDischarge (getDynamicObservables vts) scC scP'

        if all isFloatingVSC (fst scP'')
          then return $ MT n (unwrapASN asnP) (chkPatn mc partsP)
                             fbind replP scC scP' tP'
          else fail "undischargeable s.c."
  where
    chkPatn MatchEqvLHS (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  MatchEqvVar 1
    chkPatn MatchEqvRHS (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  MatchEqvVar 2
    chkPatn (MatchEqv [i]) (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  MatchEqvVar i
    chkPatn mc _                             =  mc
\end{code}

\subsection{Applying a Match}

\textbf{TODO: }
\textsf{bring match application here}

\newpage
\subsection{Undoing a Proof Step}

\textbf{
 We would like to restore focus when backing up a simple step,
 such as UseLaw.
}
\begin{code}
undoCalcStep :: LiveProof -> LiveProof
undoCalcStep liveProof
  = case stepsSoFar liveProof of
      []                       ->  liveProof
      ((just,(Assertion term sc)):prevSteps)
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

    setTerm t (tz,sequent') = (mkTZ t,sequent')
\end{code}


\newpage
\section{Making a Theorem}

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
  = (  thnm
    , ( ( nm, asn ), Proven nm )
    , ( thnm, nm, asn, strategy liveProof, calc )
    )
  where
     thnm = conjThName liveProof
     -- hack - should refer to logicSig
     equiv = fromJust $ ident "equiv"
     mkEquivs ps = Cons arbpred True equiv ps
     p === q = mkEquivs [p,q]
     step0 = assnT $ conjecture liveProof
     step' = exitTZ $ fst $ focus liveProof
     sc = conjSC liveProof
     asn = mkAsn (step0 === step') sc
     calc = ( step' , reverse $ stepsSoFar liveProof )
\end{code}

\newpage
\section{Showing Live Proofs}

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
 = unlines $
       shProof liveProof
       ++
       ( displayMatches prfSet (mtchCtxts liveProof) mtchs
         : [ "-----------("++dcount++"/"++mcount++")" -- underline "           "
           , dispSeqZip (fPath liveProof) (conjSC liveProof) (focus liveProof)
           , "XPNDD:\n"++(trSideCond $ xpndSC liveProof)
           , "" ]
       )
  where 
    prfSet = liveSettings liveProof
    mtchs = matches liveProof
    mcount = show $ length mtchs
    dmatches = take (maxMatchDisplay prfSet) mtchs
    dcount = show $ length dmatches
    (trm,sc) = unwrapASN $ conjecture liveProof


-- dispLiveProof but when proof is complete
-- temporary
dispEndProof :: LiveProof -> String
dispEndProof liveProof = unlines $ shProof liveProof


shProof :: LiveProof -> [String]
shProof liveProof
 =   ( ("\nProof for "++red (widthHack 2 $ conjName liveProof))
       : ("\t" ++ green(trTerm 0 trm ++ "\n\t"++ trSideCond sc))
       : ("by "++strategy liveProof)
       : showsteps
       ) 
 where 
   prfSet = liveSettings liveProof
   maxstep = maxStepDisplay prfSet
   allsteps = stepsSoFar liveProof
   showsteps = shProofSteps maxstep allsteps
   (trm,sc) = unwrapASN $ conjecture liveProof

shProofSteps maxstep steps
 | maxstep >= length steps  =  map shLiveStep $ reverse steps
 | otherwise  =  "..." : ( map shLiveStep $ reverse $ take maxstep steps )

shLiveStep :: CalcStep -> String
shLiveStep ( just, asn@(Assertion tm sc) )
  = unlines' [ trTerm 0 tm
             , showJustification just]

displayMatches :: ProofSettings -> [MatchContext] -> Matches -> String
displayMatches _ _ []  =  ""
displayMatches prfSet mctxts mtchs
  =  unlines' ( ("Matches:")
                : map (shMatch showbind vts) (reverse $ zip [1..] mtchs) )
  where 
    vts = concat $ map thd3 mctxts
    showbind = showBindings prfSet
    

shMatch showbind vts (i, mtch)
 = show i ++ " : "++ ldq ++ red (truelawname $ mName mtch) ++ rdq
   ++ " " ++ shMClass (mClass mtch)
   ++ showBinding showbind
   ++ lnindent ++ (bold $ blue $ trTerm 0 $ mRepl mtch)
   ++ lnindent ++ shSCImplication (mLocSC mtch) (mLawSC mtch)
 where
    lnindent = "\n    "
    showBinding False = ""
    showBinding True = lnindent ++ trBinding (mBind mtch) 
    showRepl (But msgs) = unlines ("auto-instTerm failed!!":msgs)
    showRepl (Yes brepl) = trTerm 0 brepl

-- instantiateRepl :: [VarTable] -> ProofMatch -> YesBut Term
-- instantiateRepl vts mtch
--   = case bindFloating vts bind repl of
--             But msgs   ->  But msgs
--             Yes abind  ->  instTerm abind repl
--   where
--     bind = mBind mtch
--     repl = mRepl mtch
--
-- instReplInMatch :: [VarTable] -> ProofMatch -> ProofMatch
-- instReplInMatch vts mtch
--   =  case instantiateRepl vts mtch of
--        But _      ->  mtch
--        Yes irepl  ->  mtch{mRepl = irepl}

shSCImplication scC scPm
  =     trSideCond scC
     ++ " " ++ _imp ++ " "
     ++ trSideCond scPm

shMappedCond vts scC bind lsc
  = case instantiateSC
           (mkInsCtxt vts scC) 
           bind lsc
    of
      Nothing    ->  trSideCond lsc ++ (red " (law-sc!)")
      Just ilsc  ->  trSideCond ilsc

shMClass MatchAll         =  green "[*]"
shMClass MatchEqvLHS      =  green ("["++_eqv++"lhs]")
shMClass MatchEqvRHS      =  green ("["++_eqv++"rhs]")
shMClass (MatchEqv is)    =  green ("["++_eqv++show is++"]")
shMClass MatchAnte        =  green ("[*"++_imp++" ]")
shMClass MatchCnsq        =  green ("["++_imp++" *]")
shMClass (MatchEqvVar i)  =  red ("[trivial!"++show i++"]")
\end{code}

We can display laws from a context (again, this should be done elsewhere).
\begin{code}
showContextLaws (nm,lws,_)
  = unlines' (
      [ "Theory '"++nm++"'"
      , showLaws (trTerm 0, trSideCond) lws
      ] )
\end{code}

We can display known names from a context
(again, this also should be done elsewhere).
\begin{code}
showContextKnowns (nm,_,vts)
  = unlines' (
      [ "Theory '"++nm++"'"
      , showKnowns vts
      ] )
\end{code}
