\chapter{\reasonEq\ State}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017--2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module REqState ( REqState(..), reqstate0
                , projectDir__, projectDir_
                , modified__, modified_, changed
                , theories__, theories_
                , prfSettings__, prfSettings_
                , currTheory__, currTheory_, liveProofs__, liveProofs_
                , writeREqState
                , readREqState1, readProofSettings, readREqState2
                , module TermZipper
                , module Laws
                , module Proofs
                , module Theories
                , module Sequents
                , module LiveProofs
                )
where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Utilities
import Control
import WriteRead
import TermZipper
import Laws
import Proofs
import Theories
import Sequents
import LiveProofs
import Ranking
import ProofSettings

import Debugger
\end{code}

\newpage
\section{Settings}

We divide settings into three types:
\begin{enumerate}
  \item
    Standalone settings,
    whose associated behaviour is directly implemented
    at the relevant point in the code.
  \item
   Specification settings, that specify more complex behaviour tuning,
   for which it is worth to compute behaviour once when they are changed.
  \item
   Implementation settings,
   are related to the specification settings above.
   These are never directly set by the user,
   but are computed from user-changes to the specification settings above.
   The relationship is not one-to-one.
   In particular,
   a given implementation setting may be a blend
   of several related specification settings.
\end{enumerate}


\newpage
\section{\reasonEq\ State Type}

Here we simply aggregate all the various theorem prover compoments: 
theories, proofs, settings, etc.

\begin{code}
data REqState
 = REqState {
      inDevMode   ::  Bool -- true if in development mode
    , projectDir  ::  FilePath -- current workspace directory
    , modified    ::  Bool -- True if anything modified but not saved
    -- all below are saved
    , prfSettings ::  ProofSettings
    , theories    ::  TheoryDAG
    , currTheory  ::  String
    , liveProofs  ::  LiveProofs
    }

projectDir__ f r = r{projectDir = f $ projectDir r}
projectDir_      = projectDir__ . const
modified__ f r = r{modified = f $ modified r}
modified_      = modified__ . const
changed = modified_ True
prfSettings__ f r = r{prfSettings = f $ prfSettings r}
prfSettings_      = prfSettings__ . const
theories__ f r = r{theories = f $ theories r}
theories_ = theories__ . const
currTheory__ f r = r{currTheory = f $ currTheory r}
currTheory_      = currTheory__ . const
liveProofs__ f r = r{liveProofs = f $ liveProofs r}
liveProofs_      = liveProofs__ . const

reqstate0 = REqState { inDevMode = False
                     , projectDir = ""
                     , modified = False
                     , prfSettings = initProofSettings
                     , theories = noTheories
                     , currTheory = ""
                     , liveProofs = M.empty }
\end{code}

\newpage
\section{Writing and Reading State}

\begin{code}
reqstate = "REQSTATE"
reqstateHDR = "BEGIN "++reqstate ; reqstateTLR ="END "++reqstate
currThKEY = "CURRTHEORY = "
\end{code}

\subsection{Write State}

\begin{code}
writeREqState :: REqState -> ([String],[String],NamedTheoryTexts)
writeREqState reqs
  = ( [ reqstateHDR ] ++
      thrysTxt ++
      [currThKEY ++ (currTheory reqs)] ++
      writeLiveProofs (liveProofs reqs) ++
      [ reqstateTLR ]
    , writeProofSettings (prfSettings reqs)
    , nmdTxts )
  where (thrysTxt,nmdTxts) = writeTheories (theories reqs)
\end{code}

\subsection{Read State}

We have to split this into two phases:
\begin{code}
readREqState1 :: MonadFail m => [String] -> m ([String],[String])
readREqState1 [] = fail "readREqState1: no text."
readREqState1 txts
  = do rest1 <- readThis reqstateHDR txts
       (thryNms,rest2) <- readTheories1 rest1
       return (thryNms,rest2)

readREqState2 :: MonadFail m => ProofSettings ->  [(String,Theory)]
              -> [String] -> m REqState
readREqState2 _ _ [] = fail "readREqState2: no text."
readREqState2 theSet thMap txts
  = do (thrys,rest1) <- readTheories2 thMap txts
       (cThNm,rest2) <- readKey currThKEY id rest1
       (lPrfs,rest3) <- readLiveProofs thrys rest2
       readThis reqstateTLR rest3 -- ignore any junk after trailer.
       return $ REqState { inDevMode = False
                         , projectDir = ""
                         , modified = False
                         , prfSettings = theSet
                         , theories = thrys
                         , currTheory = cThNm
                         , liveProofs = lPrfs }
\end{code}

\newpage
\section{Test Functions}

For \texttt{andIfWanted}

\begin{code}
yes _ _ = True
oddt _ = odd
event _ = even
small _ n = n < 5
big _ n = n > 10

preds     = [  oddt, event, small,   big ]

oddsmall  = [  True, False,  True, False ]
oddbig    = [  True, False, False, True  ]
evensmall = [ False,  True,  True, False ]
evenbig   = [ False,  True, False, True  ]
evens     = [ False,  True, False, False ]
contra    = [ True,   True, False, False ]

litteodd  = run $ zip oddsmall  preds
bigodd    = run $ zip oddbig    preds
tinyeven  = run $ zip evensmall preds
hugeeven  = run $ zip evenbig   preds
justevens = run $ zip evens preds
nope      = run $ zip contra preds

run spec n
 =  f [] n
 where
   f = foldl mrg yes spec
   mrg fltsofar (enabled,flt) = andIfWanted enabled flt fltsofar
\end{code}
