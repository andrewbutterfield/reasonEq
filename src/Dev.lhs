\section{Development Stuff}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Dev
( devInitState
, devBIRemind
, devListAllBuiltins
, devInstallBuiltin
, devResetBuiltin
, devUpdateBuiltin
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
import Theories
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
import UTPBase
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
            , settings = initREqSettings
            , theories = devTheories
            , currTheory = equivName
            , liveProofs = M.empty }

devKnownBuiltins  = [ equivTheory
                    , notTheory
                    , disjTheory
                    , conjTheory
                    , aoiTheory
                    , implTheory
                    , equalityTheory
                    , forallTheory
                    , existsTheory
                    , uCloseTheory
                    , utpBaseTheory
                    -- , xyzTheory
                    -- , xyzDTheory
                    ]

forceAddTheory ths th = fromJust $ addTheory th ths
devTheories = foldl forceAddTheory noTheories $ devKnownBuiltins
\end{code}

\newpage
\subsection{Development Features}

Listing builtin theories:
\begin{code}

biLkp :: String -> [Theory] -> Maybe Theory
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
  = "Remember to update Dev.devKnownBuiltins with new builtins."
\end{code}

Installing builtin theories:
\begin{code}
devInstallBuiltin :: REqState -> String -> IO (Maybe String,REqState)
devInstallBuiltin reqs thnm
  = case biLkp thnm devKnownBuiltins of
      Nothing
        -> return ( Just ("devInstallBuiltin: no builtin theory '"++thnm++"'")
                  , reqs)
      Just thry
        -> case addTheory thry $ theories reqs of
             But msgs -> return (Just $ unlines' msgs,reqs)
             Yes thrys' -> return (Nothing,changed reqs{theories=thrys'})
\end{code}

Resetting an existing theory
is only safe if the builtin version has the same dependency list
as the theory being replaced.
\begin{code}
devResetBuiltin :: REqState -> String -> IO (Maybe String,REqState)
devResetBuiltin reqs thnm
  = case biLkp thnm devKnownBuiltins of
     Nothing
      -> return ( Just ("devResetBuiltin: no builtin theory '"++thnm++"'")
                , reqs)
     Just thry0
      -> do let thrys  = theories reqs
            case replaceTheory thnm (const thry0) thrys of
              But msgs   ->  return ( Just $ unlines' msgs, reqs )
              Yes thrys' ->  return ( Nothing, changed reqs{theories=thrys'} )
\end{code}

Updating an existing theory.
This is also only safe if the builtin version has the same dependency list
as the theory being replaced.
\begin{code}
devUpdateBuiltin :: REqState -> String -> Bool -> IO (Maybe String,REqState)
devUpdateBuiltin reqs thnm force
  = case biLkp thnm devKnownBuiltins of
     Nothing
      -> return ( Just ("devUpdateBuiltin: no builtin theory '"++thnm++"'")
                , reqs)
     Just thry0
      -> do let thrys  = theories reqs
            case updateTheory thnm thry0 force thrys of
              But msgs   ->  return ( Just $ unlines' msgs, reqs )
              Yes thrys' ->  return ( Nothing, changed reqs{theories=thrys'} )
\end{code}
