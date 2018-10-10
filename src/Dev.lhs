\section{Development Stuff}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Dev (devInitState) where

import qualified Data.Map as M
import Data.Maybe
import LexBase
import Variables
import AST
import VarData
import SideCond
import REqState
import PropAxioms
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropMixOne
import PropImpl
import Equality
import PredAxioms
\end{code}

We assume the the project directory is defined as an immediate
subdirectory of the current directory from which the program
was launched.

\begin{code}
devProjectDir = "devproj"
\end{code}

We present the initial state in development mode,
which currently initialises state based on the contents of
the hard-coded ``Propositional'' theory,
plus any other test theories we choose to insert.

\begin{code}
devInitState
 = REqState { inDevMode = True
            , projectDir = devProjectDir
            , modified = False
            , settings = REqSet 20
            , logicsig = propSignature
            , theories = devTheories
            , currTheory = predAxiomName
            , liveProofs = M.empty }

devTheories
  =  fromJust $ addTheory predAxiomTheory $
     fromJust $ addTheory equalityTheory $
     fromJust $ addTheory propImplTheory $
     fromJust $ addTheory propMixOneTheory $
     fromJust $ addTheory propConjTheory $
     fromJust $ addTheory propDisjTheory $
     fromJust $ addTheory propNotTheory $
     fromJust $ addTheory propEquivTheory $
     fromJust $ addTheory propAxiomTheory noTheories
\end{code}
