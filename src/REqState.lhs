\section{\reasonEq\ State}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module REqState ( REqState(..)
                , logic__, logic_, theories__, theories_
                , currTheory__, currTheory_, liveProofs__, liveProofs_
                , writeREqState, readREqState1, readREqState2
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
import WriteRead
import TermZipper
import Laws
import Proofs
import Theories
import Sequents
import LiveProofs
\end{code}

\subsection{Prover State Type}

Here we simply aggregate the semantic equational-reasoning prover state

\begin{code}
data REqState
 = REqState {
      projectDir  ::  FilePath -- where the rest below lives
    , logicsig       ::  LogicSig
    , theories    ::  Theories
    , currTheory  ::  String
    , liveProofs  ::  LiveProofs
    }

projectDir__ f r = r{projectDir = f $ projectDir r}
projectDir_      = projectDir__ . const
logic__    f r = r{logicsig    = f $ logicsig r}    ; logic_    = logic__    . const
theories__ f r = r{theories = f $ theories r} ; theories_ = theories__ . const
currTheory__ f r = r{currTheory = f $ currTheory r}
currTheory_      = currTheory__ . const
liveProofs__ f r = r{liveProofs = f $ liveProofs r}
liveProofs_      = liveProofs__ . const
\end{code}


\subsection{Writing and Reading State}

\begin{code}
reqstate = "REQSTATE"
reqstateHDR = "BEGIN "++reqstate ; reqstateTLR ="END "++reqstate
currThKEY = "CURRTHEORY = "
\end{code}

\subsubsection{Write State}

\begin{code}
writeREqState :: REqState -> ([String],NamedTheoryTexts)
writeREqState reqs
  = ( [ reqstateHDR ] ++
      writeSignature (logicsig reqs) ++
      thrysTxt ++
      [currThKEY ++ (currTheory reqs)] ++
      writeLiveProofs (liveProofs reqs) ++
      [ reqstateTLR ]
    , nmdTxts )
  where (thrysTxt,nmdTxts) = writeTheories (theories reqs)
\end{code}

\subsubsection{Read State}

We have to split this into two phases:
\begin{code}
readREqState1 :: Monad m => [String] -> m ((LogicSig,[String]),[String])
readREqState1 [] = fail "readREqState1ß: no text."
readREqState1 txts
  = do rest1 <- readThis reqstateHDR txts
       (theSig,rest2) <- readSignature rest1
       (thryNms,rest3) <- readTheories1 rest2
       return ((theSig,thryNms),rest3)

readREqState2 :: Monad m => LogicSig -> [(String,Theory)] -> [String] -> m REqState
readREqState2 _ _ [] = fail "readREqState2: no text."
readREqState2 theSig thMap txts
  = do (thrys,rest1) <- readTheories2 thMap txts
       (cThNm,rest2) <- readKey currThKEY id rest1
       let thylist = fromJust $ getTheoryDeps cThNm thrys
       (lPrfs,rest3) <- readLiveProofs thylist rest2
       readThis reqstateTLR rest3 -- ignore any junk after trailer.
       return $ REqState { projectDir = ""
                         , logicsig = theSig
                         , theories = thrys
                         , currTheory = cThNm
                         , liveProofs = lPrfs }
\end{code}
