\chapter{Run Classified Laws}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module RunClassified
  ( applyCLA
  ) where

-- import qualified Data.Set as S
-- import Laws
-- import AST
-- import Assertions
-- import LexBase
-- import Proofs
import LiveProofs

import Debugger
\end{code}

\begin{code}
applyCLA :: MonadFail mf => LiveProof -> mf LiveProof
applyCLA liveproofs
  = fail "Automating classifiers N.Y.I."
\end{code}

