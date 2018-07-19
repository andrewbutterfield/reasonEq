\section{\reasonEq\ State}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module REqState ( REqState(..)
                , logic__, logic_, theories__, theories_
                , currTheory__, currTheory_, liveProofs__, liveProofs_
                , writeREqState, readREqState
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

import TermZipper
import Laws
import Proofs
import Theories
import Sequents
import LiveProofs
\end{code}

\subsection{Prover State Type}

Here we simply aggregate the semantic equational-reasoning prover state.

\begin{code}
data REqState
 = REqState {
      logic       ::  TheLogic
    , theories    ::  Theories
    , currTheory  ::  String
    , liveProofs  ::  LiveProofs
    }

logic__    f r = r{logic    = f $ logic r}    ; logic_    = logic__    . const
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
\end{code}

\subsubsection{Write State}

This is top-level, so expects to consume whole string.
\begin{code}
writeREqState :: REqState -> [String]
writeREqState reqs
  = [ reqstateHDR ] ++
    writeTheLogic (logic reqs) ++
    [ "writeREqState: NYFI"
    , reqstateTLR ]
\end{code}

\subsubsection{Read State}

\begin{code}
readREqState :: Monad m => [String] -> m REqState
readREqState [] = fail "readREqState: no text."
readREqState (hdr:rest1)
 | hdr /= reqstateHDR = fail "readREqState: bad header."
 | otherwise =
    do (thelogic,rest2) <- readTheLogic rest1
       fail "readREqState: NYFI"
\end{code}
