\section{Live Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LiveProofs
 ( Match(..)
 , LiveProof(..)
 , conjName__, conjName_, conjecture__, conjecture_, conjSC__, conjSC_
 , strategy__, strategy_, mtchCtxts__, mtchCtxts_, focus__, focus_
 , fPath__, fPath_, matches__, matches_, stepsSoFar__, stepsSoFar_
 , dispLiveProof
 , startProof, launchProof
 , displayMatches
 , buildMatchContext, matchInContexts
 , proofComplete, finaliseProof
 , showLivePrf
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.List
--
import Utilities
import LexBase
import Variables
import AST
import SideCond
import TermZipper
import VarData
import Binding
import Matching
import Instantiate
import Proof
import Theories
import Sequents

-- import Builder
--
import NiceSymbols
import TestRendering
--
-- import Test.HUnit hiding (Assertion)
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for the key concepts behind a live/ongoing proof.

\subsection{Proof Calculations}

We start with the simplest proof process of all,
namely a straight calculation from a starting assertion
to a specified final assertion, usually being the axiom \true.
We need to have an AST zipper to allow sub-terms to be singled out
for match and replace,
and some way of recording what happened,
so that proofs (complete or partial) can be saved,
restored, and reviewed.

The actions involved in a proof calculation step are as follows:
\begin{itemize}
  \item Select sub-term.
  \item Match against laws.
  \item Select preferred match and apply its replacement.
  \item Record step (which subterm, which law).
\end{itemize}

We need to distinguish between a `live' proof,
which involves a zipper,
and a proof `record',
that records all the steps of the proof
in enough detail to allow the proof to be replayed.

We start with live proofs:
\begin{code}
data LiveProof
  = LP {
      conjName :: String -- conjecture name
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

-- field modification boilerplate
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

data Match
 = MT { mName ::  String     -- assertion name
      , mAsn  ::  Assertion  -- matched assertion
      , mBind ::  Binding    -- resulting binding
      , mRepl ::  Term       -- replacement term
      } deriving (Eq,Show,Read)

type Matches = [Match]

-- temporary
dispLiveProof :: LiveProof -> String
dispLiveProof liveProof
 = unlines'
     ( ( ("Proof for '"++red (conjName liveProof)
          ++"'  "++trSideCond (conjSC liveProof))
       : ("by "++(strategy liveProof))
       : " ..."
       : map shLiveStep (reverse (stepsSoFar liveProof))
       )
       ++
       ( displayMatches (matches liveProof)
         : [ underline "           "
           , dispSeqZip (focus liveProof)
           , "" ]
       ) )

shLiveStep :: CalcStep -> String
shLiveStep ( just, trm )
  = unlines' [ trTerm 0 trm, showJustification just]

displayMatches :: Matches -> String
displayMatches []  =  ""
displayMatches matches
  =  unlines' ( ("Matches:") : map shMatch (zip [1..] matches))

shMatch (i, mtch)
 = ( show i ++ " : "++ ldq ++ green (mName mtch) ++ rdq
     ++ " gives     "
     ++ (bold . blue)
           ( trTerm 0 (fromJust $ instantiate bind $ mRepl mtch)
             ++ "  "
             ++ trSideCond (fromJust $ instantiateSC bind $ lsc) ) )
 where
    bind = mBind mtch
    (lt,lsc) = mAsn mtch
\end{code}


\newpage
We need to setup a proof from a conjecture:
\begin{code}
startProof :: TheLogic -> [Theory] -> String -> Assertion -> LiveProof
startProof logic thys nm asn@(t,sc)
  =  LP { conjName = nm
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
    (strat,seq) = fromJust $ reduce logic thys (nm,asn)
    sz = leftConjFocus seq
    mcs = buildMatchContext thys
\end{code}

\begin{code}
launchProof :: [Theory] -> String -> Assertion -> (String,Sequent) -> LiveProof
launchProof thys nm asn@(t,sc) (strat,seq)
  = LP { conjName = nm
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
We need to determine when a live proof is complete:
\begin{code}
proofComplete :: TheLogic -> LiveProof -> Bool
proofComplete logic liveProof
  =  let
       sequent = exitSeqZipper $ focus liveProof
       hypTerms = map (fst . snd . fst) $ laws $ hyp sequent
     in cleft sequent == cright sequent -- should be alpha-equivalent
        ||
        any (== theFalse logic) hypTerms
\end{code}

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
  = ( [Law]        -- all laws of this theory
    , [VarTable] ) -- all known variables here, and in dependencies
\end{code}

Given a list of theories, we generate a list of match-contexts:
\begin{code}
buildMatchContext :: [Theory] -> [MatchContext]
buildMatchContext [] = []
buildMatchContext [thy] = [ (laws thy, [knownVars thy]) ]
buildMatchContext (thy:thys)
  = let mcs'@((_,vts'):_) = buildMatchContext thys
    in (laws thy, knownVars thy : vts') : mcs'
\end{code}

\newpage
\subsection{Assertion Matching}

First, given list of match-contexts, systematically work through them.
\begin{code}
matchInContexts :: TheLogic -> [MatchContext] -> Term -> Matches
matchInContexts logic mcs t
  = concat $ map (matchLaws logic t) mcs
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: TheLogic -> Term -> MatchContext -> Matches
matchLaws logic t (lws,vts) = concat $ map (domatch logic vts t) lws
\end{code}

For each law,
we check its top-level to see if it is an instance of \texttt{theEqv},
in which case we try matches against all possible variations.
\begin{code}
domatch :: TheLogic -> [VarTable] -> Term -> Law -> Matches
domatch logic vts tC ((n,asn@(tP@(Cons tk i ts@(_:_:_)),sc)),prov)
  | i == theEqv logic  =  concat $ map (eqvMatch vts tC) $ listsplit ts
  where
      -- tC :: equiv(tsP), with replacement equiv(tsR).
    eqvMatch vts tC (tsP,tsR)
      = justMatch (eqv tsR) vts tC ((n,(eqv tsP,sc)),prov)
    eqv []   =  theTrue logic
    eqv [t]  =  t
    eqv ts   =  Cons tk i ts
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch logic vts tC law
 = justMatch (theTrue logic) vts tC law
\end{code}

Do a simple match:
\begin{code}
justMatch :: Term -> [VarTable] -> Term -> Law -> Matches
justMatch repl vts tC ((n,asn@(tP,_)),_)
 = case match vts tC tP of
     Nothing -> []
     Just bind -> [MT n asn bind repl]
\end{code}

\newpage
\subsection{Showing stuff}

\textbf{This should all be done via proper generic rendering code}


Showing Proof:
\begin{code}
showLivePrf Nothing = "no Proof."
showLivePrf (Just proof) = dispLiveProof proof
\end{code}
