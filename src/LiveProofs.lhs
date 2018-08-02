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
 , conjThName__, conjThName_, conjName__, conjName_
 , conjecture__, conjecture_, conjSC__, conjSC_
 , strategy__, strategy_, mtchCtxts__, mtchCtxts_, focus__, focus_
 , fPath__, fPath_, matches__, matches_, stepsSoFar__, stepsSoFar_
 , LiveProofs
 , writeLiveProofs, readLiveProofs
 , dispLiveProof
 , startProof, launchProof
 , displayMatches
 , buildMatchContext, matchInContexts
 , proofIsComplete, finaliseProof
 , showLiveProofs
 ) where

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M

import Utilities
import WriteRead
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
buildMatchContext [thy] = [ (laws thy, [known thy]) ]
buildMatchContext (thy:thys) -- thys not null
  = let mcs'@((_,vts'):_) = buildMatchContext thys
    in (laws thy, known thy : vts') : mcs'
\end{code}

\subsection{Matches}

\begin{code}
data Match
 = MT { mName ::  String     -- assertion name
      , mAsn  ::  Assertion  -- matched assertion
      , mBind ::  Binding    -- resulting binding
      , mRepl ::  Term       -- replacement term
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


\subsection{Live Proof Collection}

We maintain a collection of \texttt{LiveProof}s
as a map from theory and conjecture names to the corresponding live proof:
\begin{code}
type LiveProofs = Map (String,String) LiveProof
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


\subsection{Assertion Matching}

First, given list of match-contexts, systematically work through them.
\begin{code}
matchInContexts :: LogicSig -> [MatchContext] -> Term -> Matches
matchInContexts logicsig mcs t
  = concat $ map (matchLaws logicsig t) mcs
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: LogicSig -> Term -> MatchContext -> Matches
matchLaws logicsig t (lws,vts) = concat $ map (domatch logicsig vts t) lws
\end{code}

For each law,
we check its top-level to see if it is an instance of \texttt{theEqv},
in which case we try matches against all possible variations.
\begin{code}
domatch :: LogicSig -> [VarTable] -> Term -> Law -> Matches
domatch logicsig vts tC ((n,asn@(tP@(Cons tk i ts@(_:_:_)),sc)),prov)
  | i == theEqv logicsig  =  concat $ map (eqvMatch vts tC) $ listsplit ts
  where
      -- tC :: equiv(tsP), with replacement equiv(tsR).
    eqvMatch vts tC (tsP,tsR)
      = justMatch (eqv tsR) vts tC ((n,(eqv tsP,sc)),prov)
    eqv []   =  theTrue logicsig
    eqv [t]  =  t
    eqv ts   =  Cons tk i ts
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch logicsig vts tC law
 = justMatch (theTrue logicsig) vts tC law
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
