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
 , showLiveProofs
 , showContextLaws
 ) where

import Data.Maybe
import Data.List
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
 = MT { mName ::  String     -- assertion name
      , mAsn  ::  Assertion  -- matched assertion
      , mClass :: MatchClass -- match class
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

\newpage
\subsubsection{Trying a Match}

Sometimes we want to what happens when we single out a law,
including observing any match failure messages.
Here we painstakingly check every monadic call from \texttt{match} onwards,
and report the outcome.
\begin{code}
tryLawByName :: LogicSig -> Assertion -> String -> [Int] -> [MatchContext]
               -> YesBut Binding
tryLawByName logicsig asn@(tC,scC) lnm parts mcs
  = do (((_,(tP,scP)),_),vts) <- findLaw lnm mcs
       partsP <- findParts parts $ pdbg "tP" tP
       tryMatch vts tP partsP scP
  where
\end{code}

First, try the structural match.
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    tryMatch vts tP partsP scP
      = case match vts (pdbg "tC" tC) $ pdbg "partsP" partsP of
          Yes bind  ->  tryInstantiateSC bind tP partsP scP
          But msgs
           -> But  [ "tryMatch failed"
                   , ""
                   , trTerm 0 tC ++ " :: " ++ trTerm 0 partsP
                   , ""
                   , "lnm[parts]="++lnm++show parts
                   , "tC="++trTerm 0 tC
                   , "scC="++trSideCond scC
                   , "tP="++trTerm 0 tP
                   , "partsP="++trTerm 0 partsP
                   , ""
                   ]
\end{code}

Missing, the phase where we deal with unbound/unmatched variables
from the rest of the pattern-law.

Next, instantiate the pattern side-condition using the bindings.
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    tryInstantiateSC bind tP partsP scP
      = do  scP' <- instantiateSC (dbg "bind" bind) $ pdbg "scP" scP
            trySCDischarge bind tP partsP scP scP'
\end{code}

Finally, try to discharge the instantiated side-condition:
\begin{code}
-- tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    trySCDischarge bind tP partsP scP scP'
      = do  if scDischarged (pdbg "scC" scC) $ pdbg "scP'" scP'
              then Yes bind
              else But [ "tryLawByName failed"
                       , "lnm[parts]="++lnm++show parts
                       , "tC="++trTerm 0 tC
                       , "scC="++trSideCond scC
                       , "tP="++trTerm 0 tP
                       , "partsP="++trTerm 0 partsP
                       , "scP="++trSideCond scP
                       , "scP'="++trSideCond scP'
                       , "bind:\n"
                       , trBinding bind
                       ]
\end{code}

Done.
\begin{code}
-- end tryLawByName
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

-- assume all ints positive
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

Looking up a law by name:
\begin{code}
findLaw :: Monad m => String -> [MatchContext] -> m (Law,[VarTable])
findLaw lnm [] = fail ("Law '"++lnm++"' not found")
findLaw lnm ((thnm,lws,vts):mcs)
 = case filter (\law -> lawName law == lnm) lws of
     []       ->  findLaw lnm mcs
     (law:_)  ->  return (law,vts)
\end{code}

\newpage
\subsection{Assertion Matching}

For each law,
we check its top-level to see if it is an instance of \texttt{theEqv},
in which case we try matches against all possible variations,
as well as the whole thing.
\begin{code}
domatch :: LogicSig -> [VarTable] -> Assertion -> Law -> Matches
domatch logicsig vts asnC law@((nP,asn@(tP@(Cons tk i tsP@(_:_:_)),scP)),prov)
  | i == theEqv logicsig  =  simpleMatch MatchAll (theTrue logicsig) vts asnC law
                             ++ doEqvMatch logicsig vts asnC nP prov scP tsP
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch logicsig vts asnC law
  =  simpleMatch MatchAll (theTrue logicsig) vts asnC law
\end{code}

Do a simple match.
Here is where we do side-condition checking.
\begin{code}
simpleMatch :: MatchClass -> Term -> [VarTable] -> Assertion -> Law -> Matches
simpleMatch mc repl vts asnC@(tC,scC) ((n,asn@(tP,scP)),_)
  = concat $ map (mkmatch scC scP) $ match vts tC tP
  where
    mkmatch scC scP bind
      =  do scP' <- instantiateSC bind scP
            -- does scC ==> scP' ?
            if scDischarged scC scP'
            then
              case instantiate bind repl of
                Nothing     ->  []
                Just irepl  ->  [MT n asn (chkPatn mc tP) bind irepl]
            else []

    chkPatn mc (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  trivialise mc
    chkPatn mc _                             =  mc

trivialise (MatchEqv [i])  =  MatchEqvVar i
trivialise mc              =  mc
\end{code}

\newpage
Do an equivalence match, where we want to match against all possibilities,
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

First, Case A, which is automatically done above by \texttt{simpleMatch},
so we need not return any matches here.
\begin{code}
doEqvMatch _ _ _ _ _ _ [tP1,tP2] | tP1 == tP2  =  []
\end{code}
Then invoke Cases C and B, in that order.
\begin{code}
doEqvMatch logicsig vts asnC nP prov scP  tsP
  = doEqvMatchC logicsig vts asnC nP prov scP tsP
    ++
    doEqvMatchB logicsig vts asnC nP prov scP [] [] tsP
\end{code}

Next, Case B.
\begin{code}
doEqvMatchB logicsig vts asnC nP prov scP mtchs _ [] = mtchs
doEqvMatchB logicsig vts asnC nP prov scP mtchs sPt (tP:tPs)
  = let mtchs' = simpleMatch (MatchEqv [length sPt + 1])
                    (eqv (reverse sPt ++ tPs)) vts asnC ((nP,(tP,scP)),prov)
    in doEqvMatchB logicsig vts asnC nP prov scP (mtchs'++mtchs) (tP:sPt) tPs
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
doEqvMatchC logicsig vts asnC@(tC@(Cons tk i tsC),scC) nP prov scP tsP
 | i == theEqv logicsig
   && cLen < pLen  = doEqvMatchC' cLen [1..cLen]
                       logicsig vts scC nP prov scP  tsC tsP
                     ++
                     doEqvMatchC' cLen [pLen+1-cLen .. pLen]
                       logicsig vts scC nP prov scP (reverse tsC) (reverse tsP)
 where
    cLen = length tsC
    pLen = length tsP
doEqvMatchC _ _ _ _ _ _ _ = []

-- we assume cLen < pLen here
doEqvMatchC' cLen is logicsig vts scC nP prov scP tsC tsP
  = simpleMatch (MatchEqv is) (eqv tsP'') vts (eqv tsC,scC)
                                              ((nP,(eqv tsP',scP)),prov)
  where
    (tsP',tsP'') = splitAt cLen tsP
    eqv []   =  theTrue logicsig
    eqv [t]  =  t
    eqv ts   =  Cons P (theEqv logicsig) ts
\end{code}

\subsubsection{Undoing a Proof Step}

\begin{code}
undoCalcStep :: LiveProof -> LiveProof
undoCalcStep liveProof
  = case stepsSoFar liveProof of
      []                       ->  liveProof
      ((just,(term,_)):prevSteps)
        ->  matches_ []
            $ fPath_ []
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

    undoCalcStep' _  = liveProof

    setTerm t (tz,seq') = (mkTZ t,seq')
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
     ( ( ("Proof for "++red (conjName liveProof))
       : ("\t" ++ green(trTerm 0 trm ++ "  "++trSideCond sc))
       : ("by "++(strategy liveProof))
       : map shLiveStep (reverse (stepsSoFar liveProof))
       )
       ++
       ( " ..."
         : displayMatches (matches liveProof)
         : [ underline "           "
           , dispSeqZip (focus liveProof)
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
 = show i ++ " : "++ ldq ++ green (mName mtch) ++ rdq
   ++ "  gives  "
   ++ (bold $ blue $ trTerm 0 (mRepl mtch))
   ++ "  "++ shSideCond bind lsc
   ++ " " ++ shMClass (mClass mtch)
 where
    bind = mBind mtch
    (_,lsc) = mAsn mtch

shSideCond bind lsc
  = case instantiateSC bind lsc of
      Nothing    ->  trSideCond lsc ++ (red " (law-sc!)")
      Just ilsc  ->  trSideCond ilsc

shMClass MatchAll         =  green "*"
shMClass (MatchEqv is)    =  green (_equiv++show is)
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
