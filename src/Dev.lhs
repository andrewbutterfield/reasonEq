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
import Propositions
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
 = REqState { projectDir = devProjectDir
            , logic = thePropositionalAxioms
            , theories = testTheories
            , currTheory = (thName propAxiomTheory)
            , liveProofs = M.empty }

testTheories
  =  fromJust $ addTheory testTheory $
     fromJust $ addTheory propAxiomTheory noTheories

a = fromJust $ pVar $ Vbl (fromJust $ ident "A") PredV Static
b = fromJust $ pVar $ Vbl (fromJust $ ident "B") PredV Static
c = fromJust $ pVar $ Vbl (fromJust $ ident "C") PredV Static

cjHTest
 = ( "h-test"
   , ( a /\ (b /\ c) ==> (c /\ a) /\ (mkEquivs [b,b,b])
     , scTrue ) )

testName = "TestFortyTwo"

testTheory
  = Theory { thName  =  testName
           , thDeps  =  [ thName propAxiomTheory ]
           , known   =  newVarTable
           , laws    =  []
           , proofs  =  []
           , conjs   =  [ cjHTest ]
           }
\end{code}
