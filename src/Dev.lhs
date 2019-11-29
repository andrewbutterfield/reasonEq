\section{Development Stuff}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Dev
( devInitState
, devBIRemind, devListAllBuiltins, devInstallBuiltin
)
where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Utilities
import LexBase
import Variables
import AST
import VarData
import SideCond
import REqState
import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import Implication
import Equality
import ForAll
import Exists
import UClose
\end{code}

\subsection{Introduction}

We assume the the development project directory is defined as an immediate
subdirectory called \texttt{devproj}
of the current directory from which the program was launched.

\begin{code}
devProjectDir = "devproj"
\end{code}

We present the initial state in development mode,
which currently initialises state as having
the standard logic signature defined,
and all builtin theories installed.
\begin{code}
devInitState
 = REqState { inDevMode = True
            , projectDir = devProjectDir
            , modified = False
            , settings = REqSet 40
            , logicsig = propSignature
            , theories = devTheories
            , currTheory = equivName
            , liveProofs = M.empty }

devTheories =
     -- fromJust $ addTheory predUnivTheory $
     fromJust $ addTheory existsTheory $
     fromJust $ addTheory forallTheory $
     fromJust $ addTheory equalityTheory $
     fromJust $ addTheory implTheory $
     fromJust $ addTheory aoiTheory $
     fromJust $ addTheory conjTheory $
     fromJust $ addTheory disjTheory $
     fromJust $ addTheory notTheory $
     fromJust $ addTheory equivTheory
                          noTheories
\end{code}

\newpage
\subsection{Development Features}

Listing builtin theories:
\begin{code}
devKnownBuiltins  = [ equivTheory
                    , notTheory
                    , disjTheory
                    , conjTheory
                    , aoiTheory
                    , implTheory
                    , equalityTheory
                    , forallTheory
                    , existsTheory
                    -- , predUnivTheory
                    -- , utpStartupTheory
                    -- , xyzTheory
                    -- , xyzDTheory
                    ]

biLkp _ []  = Nothing
biLkp nm (th:ths)
 | nm == thName th  =  Just th
 | otherwise        =  biLkp nm ths

devListAllBuiltins :: String
devListAllBuiltins
  = summarise $ map thName devKnownBuiltins
  where
       summarise = intercalate " ; "
    -- summarise = unlines'

devBIRemind :: String
devBIRemind
  = "Remember to update AbstractUI.devKnownBuiltins with new builtins."
\end{code}

Installing builtin theories:
\begin{code}
devInstallBuiltin :: REqState -> String -> IO (Maybe String,REqState)
devInstallBuiltin reqs nm
  = case biLkp nm devKnownBuiltins of
      Nothing
        -> return ( Just ("devInstallBuiltin: no builtin theory '"++nm++"'")
                  , reqs)
      Just thry
        -> case addTheory thry $ theories reqs of
             But msgs -> return (Just $ unlines' msgs,reqs)
             Yes thrys' -> return (Nothing,changed reqs{theories=thrys'})
\end{code}
