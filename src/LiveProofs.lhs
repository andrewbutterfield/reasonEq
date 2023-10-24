\chapter{Live Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018-2022

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
 , dispEndProof
 , launchProof
 , displayMatches
 -- , instantiateRepl, instReplInMatch
 , buildMatchContext, matchInContexts, matchLawByName, tryLawByName
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

import Symbols
import TestRendering

import Debugger
\end{code}

\newpage
\section{Matching Contexts}

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

\section{Matches}

\begin{code}
data Match
 = MT { mName    ::  String     -- assertion name
      , mAsn     ::  TermSC     -- matched assertion
      , mClass   ::  MatchClass -- match class
      , mBind    ::  Binding    -- resulting binding
      , mLawPart ::  Term       -- replacement term from law
      , mLocSC   ::  SideCond   -- goal side-condition local update
      , mLawSC   ::  SideCond   -- law side-condition mapped to goal
      , mRepl    ::  Term       -- replacement term, instantiated with binding
      } deriving (Eq,Show,Read)

type Matches = [Match]
\end{code}

\newpage
\section{Live Proof Type}

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

readLiveProof :: (Monad m, MonadFail m) => [Theory] -> [String] -> m (LiveProof,[String])
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
\section{Writing and Reading Live Proofs}

\begin{code}
liveproofs = "LIVE-PROOFS"
lprfsHDR = "BEGIN "++liveproofs ; lprfsTRL ="END "++liveproofs

lprfsKEY = "LIVEPROOFS = "

writeLiveProofs :: LiveProofs -> [String]
writeLiveProofs liveProofs
  = [ lprfsHDR ] ++
    writeMap liveproofs writeLiveProof liveProofs ++
    [ lprfsTRL ]

readLiveProofs :: (Monad m, MonadFail m) => [Theory] -> [String] -> m (LiveProofs,[String])
readLiveProofs thylist txts
  = do rest1         <- readThis lprfsHDR txts
       (lprfs,rest2) <- readMap liveproofs rdKey (readLiveProof thylist) rest1
       rest3         <- readThis lprfsTRL rest2
       return (lprfs,rest3)
\end{code}


\newpage
\section{Proof Starting and Stopping}

% \subsection{Starting a Proof with default strategy}


% We need to setup a proof from a conjecture:
% \begin{code}
% startProof :: [Theory] -> String -> String -> Assertion -> LiveProof
% startProof thys thnm cjnm asn@(Assertion t sc)
%   =  LP { conjThName = thnm
%         , conjName = cjnm
%         , conjecture = asn
%         , conjSC = sc
%         , strategy = strat
%         , mtchCtxts =  mcs
%         , focus =  sz
%         , fPath = []
%         , matches = []
%         , stepsSoFar = []
%         }
%   where
%     (strat,sequent) = fromJust $ reduce thys (cjnm,(t,sc))
%     sz = leftConjFocus sequent
%     mcs = buildMatchContext thys
% \end{code}

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
       , focus =  sz
       , fPath = []
       , matches = []
       , stepsSoFar = []
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
  = ( conjName liveProof
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
mergeBindings instantiate
\end{verbatim}
and $<$Complete Binding$>$ for application involves(?) \texttt{completeBind}.

\begin{code}
tryLawByName :: Assertion -> String -> [Int] -> [MatchContext]
               -> YesBut ( Binding    -- mapping from pattern to candidate
                         , Term       -- autoInstantiated Law
                         , SideCond   -- updated candidate side-condition
                         , SideCond ) -- discharged(?) law side-condition
tryLawByName asn@(Assertion tC scC) lnm parts mcs
  = do (((_,asnP),_),vts) <- findLaw lnm mcs
       let tP = assnT asnP
       partsP <- findParts parts tP
       tryMatch vts tP partsP $ assnC asnP
  where
    -- below we try to do:
    -- bind          <- match vts tC partsP
    -- (kbind,tPasC) <- bindKnown vts bind tP
    -- (fbind,_)     <- bindFloating vts kbind tP
    -- tP'           <- instantiate fbind tP
    -- scP'          <- instantiateSC fbind scP of
    -- scP''         <- scDischarge scC scP' of
    -- return (fbind,tP',scP',scP'')
\end{code}

First, try the structural match.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryMatch vts tP partsP scP
      = case
                match vts tC partsP
        of
          Yes bind  ->  tryInstantiateKnown vts tP partsP scP bind
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
                   , "---"
                   ]++msgs)
\end{code}

\newpage
At this point the replacement may contain variables not present in the
matched part, so we need to create temporary bindings for these.
First we see if any of these are ``known''.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiateKnown vts tP partsP scP bind
      = case
                bindKnown vts bind tP
        of
          Yes kbind  ->  tryInstantiateFloating vts tP partsP scP kbind
          But msgs
           -> But ([ "instantiate knowns failed"
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
                   ]++msgs)
\end{code}

Anything unbound and not ``known'' is ``floating'',
and we generate names for these that make their floating nature visible.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiateFloating vts tP partsP scP bind
      = case
                bindFloating vts bind tP
        of
          Yes fbind  ->  tryInstantiate
                           (mkInsCtxt scTrue) 
                           fbind tP partsP scP
          But msgs
           -> But ([ "instantiate floating failed"
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
                   ]++msgs)
\end{code}


Next, instantiate the law using the bindings.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiate insctxt fbind tP partsP scP
      = case
                instantiate insctxt fbind tP
        of
          Yes tP'  ->  tryInstantiateSC insctxt fbind tP' partsP scP
          But msgs
           -> But ([ "try law instantiation failed"
                   , ""
                   , trBinding fbind ++ "("++trSideCond scP++")"
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
Next, instantiate the pattern side-condition using the bindings.
\begin{code}
-- tryLawByName asn@(tC,scC) lnm parts mcs
    tryInstantiateSC insctxt bind tP partsP scP
      = case
                instantiateSC insctxt bind scP
        of
          Yes scP'  ->  trySCDischarge insctxt bind tP partsP scP'
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
-- tryLawByName asn@(tC,scC) lnm parts mcs
    trySCDischarge insctxt bind tP partsP scP'
      = case
                scDischarge ss scC scP'
        of
          Yes scP'' -> Yes (bind,tP,scP',scP'')
          But whynots -> But [ "try s.c. discharge failed"
                             , unlines' whynots
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
     where ss = S.elems $ S.map theSubscript $ S.filter isDuring
                          $ S.map gvarWhen $ mentionedVars tC
\end{code}

Done.
\begin{code}
-- end tryLawByName
\end{code}

\newpage
\subsection{Finding parts of laws}

Looking up a law by name:
\begin{code}
findLaw :: (Monad m, MonadFail m) => String -> [MatchContext] -> m (Law,[VarTable])
findLaw lnm [] = fail ("Law '"++lnm++"' not found")
findLaw lnm ((thnm,lws,vts):mcs)
 = case filter (\law -> lawName law == lnm) lws of
     []       ->  findLaw lnm mcs
     (law:_)  ->  return (law,vts)
\end{code}

Finding `parts' of a top-level constructor:
\begin{code}
findParts :: (Monad m, MonadFail m) => [Int] -> Term -> m Term
findParts [] t = return t
findParts parts (Cons tk sn n ts)
  = do ts' <- getParts (filter (>0) parts) ts
       case ts' of
         [t']  ->  return t'
         _     ->  return $ Cons tk sn n ts'
findParts parts t
          = fail ("findParts: "++trTerm 0 t++" "++show parts++" makes no sense")
\end{code}

Assume all \texttt{Int}s are positive and non-zero
\begin{code}
getParts :: (Monad m, MonadFail m) => [Int] -> [a] -> m [a]
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
\section{Matching in Context}

First, given list of match-contexts, systematically work through them.
\begin{code}
matchInContexts :: [MatchContext] -> Assertion -> Matches
matchInContexts mcs asn
  = concat $ map (matchLaws asn) mcs
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: Assertion -> MatchContext -> Matches
matchLaws asn (_,lws,vts)
  = concat $ map (domatch vts $ unwrapASN asn) lws
\end{code}

Sometimes we are interested in a specific (named) law.
\begin{code}
matchLawByName :: (Monad m, MonadFail m)
               => Assertion -> String -> [MatchContext]
               -> m Matches
matchLawByName asn lnm mcs
 = do (law,vts) <- findLaw lnm mcs
      return $ domatch vts (unwrapASN asn) law
\end{code}

For each law,
we match the whole thing,
and if its top-level is a \texttt{Cons}
with at least two sub-components, we try all possible partial matches.
\begin{code}
domatch :: [VarTable] -> TermSC -> Law -> Matches
domatch vts asnC law@((_,(Assertion tP@(Cons _ _ i tsP@(_:_:_)) _)),_)
  =    basicMatch MatchAll vts law theTrue asnC tP
    ++ doPartialMatch i vts law asnC tsP
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch vts asnC law@((_,(Assertion tP _)),_)
  =  basicMatch MatchAll vts law theTrue asnC tP
\end{code}


\newpage
\section{Assertion Matching}

\subsection{Partial Matching}

Here we have a top-level \texttt{Cons}
with at least two sub-terms.
\begin{code}
doPartialMatch :: Identifier -> [VarTable]
               -> Law -> TermSC -> [Term]
               -> Matches
\end{code}

First, if we have $\equiv$ we call an $n$-way equivalence matcher:
\begin{code}
doPartialMatch i vts law asnC tsP
  | i == theEqv  =   doEqvMatch vts law asnC tsP
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
doPartialMatch i vts law asnC tsP@[ltP,rtP]
  | i == theImp
    =    basicMatch MatchAnte vts law (Cons P True theAnd [ltP,rtP]) asnC ltP
      ++ basicMatch MatchCnsq vts law (Cons P True theOr  [rtP,ltP]) asnC rtP
\end{code}

Anything else won't match (right now we don't support $\impliedby$).
\begin{code}
doPartialMatch i vts law asnC tsP
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
doEqvMatch :: [VarTable] -> Law -> TermSC
           -> [Term]    -- top-level equivalence components in law
           -> Matches
doEqvMatch vts law asnC [tP1,tP2]
-- rule out matches against one-side of the reflexivity axiom
  | tP1 == tP2  =  []
-- otherwise treat binary equivalence specially:
  | otherwise  =     basicMatch MatchEqvLHS vts law tP2 asnC tP1
                  ++ basicMatch MatchEqvRHS vts law tP1 asnC tP2
\end{code}
Then invoke Cases C and B, in that order.
\begin{code}
doEqvMatch vts law asnC tsP
  = doEqvMatchC vts law asnC tsP
    ++
    doEqvMatchB vts law asnC [] [] tsP
\end{code}

Next, Case B.
\begin{code}
doEqvMatchB vts law asnC mtchs _ [] = mtchs
doEqvMatchB vts law@((_,(Assertion _ scP)),_) asnC mtchs sPt (tP:tPs)
  = let mtchs' = basicMatch (MatchEqv [length sPt + 1])
                     vts law (eqv (reverse sPt ++ tPs)) asnC tP
    in doEqvMatchB vts law asnC (mtchs'++mtchs) (tP:sPt) tPs
  where
    eqv []   =  theTrue
    eqv [t]  =  t
    eqv ts   =  Cons P True theEqv ts
\end{code}

\newpage
Case C only applies if the \emph{candidate} is an equivalence.
We will assume $m < n$ and just try $J$ being either
the first $m$ pattern components ($\setof{1\dots m}$),
or the last $m$ (\setof{n+1-m\dots n}).
\begin{code}
-- doEqvMatchC vts law asnC tsP
doEqvMatchC :: [VarTable] -> Law -> TermSC ->[Term]
            -> Matches
doEqvMatchC vts law@((_,(Assertion _ scP)),_)
                         asnC@(tC@(Cons tk si i tsC),scC) tsP
 | i == theEqv
   && cLen < pLen  = doEqvMatchC' cLen [1..cLen]
                       vts law scC tsC tsP
                     ++
                     doEqvMatchC' cLen [pLen+1-cLen .. pLen]
                       vts law scC (reverse tsC) (reverse tsP)
 where
    cLen = length tsC
    pLen = length tsP
doEqvMatchC _ _ _ _ = []

-- we assume cLen < pLen here
doEqvMatchC' :: Int -> [Int] -> [VarTable] -> Law
             -> SideCond -> [Term] -> [Term]
             -> Matches
doEqvMatchC' cLen is vts law@((_,(Assertion _ scP)),_) scC tsC tsP
  = basicMatch (MatchEqv is) vts law (eqv tsP'') (eqv tsC,scC) (eqv tsP')
  where
    (tsP',tsP'') = splitAt cLen tsP
    eqv []   =  theTrue 
    eqv [t]  =  t
    eqv ts   =  Cons P True theEqv ts
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

Process:
\begin{eqnarray*}
   \beta' &=& usercomplete(R,G(C),\beta_0)
\\ SCL' &=& \beta'(SCL)
\\ sc &=& discharge(SCG\implies SCL')
\\ C' &=&\beta'(C)
\\ G(C') &=& G(C)[C'/C]
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
            -> Law        -- law of interest
            -> Term       -- sub-part of law not being matched
            -> TermSC  -- candidate assertion
            -> Term       -- sub-part of law being matched
            -> Matches
basicMatch mc vts law@((n,asn@(Assertion tP scP)),_) repl asnC@(tC,scC) partsP
  =  do bind <- match vts tC partsP
        kbind <- bindKnown vts bind repl
        fbind <- bindFloating vts kbind repl
        let ictxt = mkInsCtxt scTrue
        scPinC <- instantiateSC ictxt fbind scP
        scD <- scDischarge ss scC scPinC

        if all isFloatingASC (fst scD)
          then do mrepl <- instantiate ictxt fbind repl
                  return $ MT n (unwrapASN asn) (chkPatn mc partsP)
                              fbind repl scC scPinC mrepl
          else fail "undischargeable s.c."
  where
    ss = S.elems $ S.map theSubscript $ S.filter isDuring
                 $ S.map gvarWhen $ mentionedVars tC

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
  = (  conjThName liveProof
    , ( ( nm, asn ), Proven nm )
    , ( nm, asn, strategy liveProof, calc )
    )
  where
     -- hack - should refer to logicSig
     equiv = fromJust $ ident "equiv"
     mkEquivs ps = PCons True equiv ps
     p === q = mkEquivs [p,q]
     step0 = assnT $ conjecture liveProof
     step' = exitTZ $ fst $ focus liveProof
     sc = conjSC liveProof
     asn = fromJust $ mkAsn (step0 === step') sc
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
dispLiveProof :: Int -> LiveProof -> String
dispLiveProof maxm liveProof
 = unlines $
       shProof liveProof
       ++
       ( " ..."
         : displayMatches maxm (mtchCtxts liveProof) (matches liveProof)
         : [ underline "           "
           , dispSeqZip (fPath liveProof) (conjSC liveProof) (focus liveProof)
           , "" ]
       )
 where (trm,sc) = unwrapASN $ conjecture liveProof


-- dispLiveProof but when proof is complete
-- temporary
dispEndProof :: LiveProof -> String
dispEndProof liveProof = unlines $ shProof liveProof


shProof :: LiveProof -> [String]
shProof liveProof
 =   ( ("\nProof for "++red (widthHack 2 $ conjName liveProof))
       : ("\t" ++ green(trTerm 0 trm ++ "  "++ trSideCond sc))
       : ("by "++strategy liveProof)
       : map shLiveStep (reverse (stepsSoFar liveProof))
       ) 
 where (trm,sc) = unwrapASN $ conjecture liveProof

shLiveStep :: CalcStep -> String
shLiveStep ( just, asn )
  = unlines' [ trAsn asn
             , showJustification just]

displayMatches :: Int -> [MatchContext] -> Matches -> String
displayMatches _ _ []  =  ""
displayMatches maxm mctxts matches
  =  unlines' ( ("Matches:")
                : map (shMatch vts) (reverse $ take maxm $ zip [1..] matches) )
  where vts = concat $ map thd3 mctxts

shMatch vts (i, mtch)
 = show i ++ " : "++ ldq ++ green (nicelawname $ mName mtch) ++ rdq
   ++ " "
   ++ (bold $ blue $ trTerm 0 $ mRepl mtch)
   ++ "  " ++ shSCImplication (mLocSC mtch) (mLawSC mtch)
   ++ " " ++ shMClass (mClass mtch)
 where
    -- bind = mBind mtch
    -- repl = mRepl mtch
    -- arepl = case bindFloating vts bind repl of
    --           But msgs   ->  But msgs
    --           Yes abind  ->  instantiate abind repl
    -- (_,lsc) = mAsn mtch
    showRepl (But msgs) = unlines ("auto-instantiate failed!!":msgs)
    showRepl (Yes brepl) = trTerm 0 brepl

-- instantiateRepl :: [VarTable] -> Match -> YesBut Term
-- instantiateRepl vts mtch
--   = case bindFloating vts bind repl of
--             But msgs   ->  But msgs
--             Yes abind  ->  instantiate abind repl
--   where
--     bind = mBind mtch
--     repl = mRepl mtch
--
-- instReplInMatch :: [VarTable] -> Match -> Match
-- instReplInMatch vts mtch
--   =  case instantiateRepl vts mtch of
--        But _      ->  mtch
--        Yes irepl  ->  mtch{mRepl = irepl}

shSCImplication scC scPm
  =     trSideCond scC
     ++ " " ++ _implies ++ " "
     ++ trSideCond scPm

shMappedCond scC bind lsc
  = case instantiateSC
           (mkInsCtxt scTrue) 
           bind lsc
    of
      Nothing    ->  trSideCond lsc ++ (red " (law-sc!)")
      Just ilsc  ->  trSideCond ilsc

shMClass MatchAll         =  green "*"
shMClass MatchEqvLHS      =  green (_equiv++"lhs")
shMClass MatchEqvRHS      =  green (_equiv++"rhs")
shMClass (MatchEqv is)    =  green (_equiv++show is)
shMClass MatchAnte        =  green ("* "++_implies)
shMClass MatchCnsq        =  green (_implies++"  *")
shMClass (MatchEqvVar i)  =  red ("trivial!"++show i)
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
