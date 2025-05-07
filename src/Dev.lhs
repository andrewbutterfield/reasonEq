\section{Development Stuff}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017--18

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

import YesBut
import Utilities
import LexBase
import Variables
import AST
import VarData
import SideCond
import Theories
import ProofSettings
import REqState
import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import Implication
import ForAll
import Exists
import UClose
import LTL
import Equality
import Arithmetic
import Sets
import Lists
import UTP.While.Common
import UTP.While.Naive
import UTP.Designs
import UTP.UTCP

import Debugger
\end{code}


\subsection{Introduction}

This module provides behaviours that are only enabled if the prover 
is started in ``development mode''.
The precise behaviour of enabling development mode may change over time.

\subsection{Development State}

\subsubsection{Directory}

We assume the the development project directory is defined as an immediate
subdirectory called \texttt{devproj}
of the current directory from which the program was launched.

\begin{code}
devProjectDir = "devproj"
\end{code}

\newpage
\subsubsection{Initial State}

We present the initial state in development mode,
which currently initialises state as having
the standard logic signature defined,
and all builtin theories installed.
\begin{code}
devInitState
 = REqState { inDevMode = True
            , projectDir = devProjectDir
            , modified = False
            , prfSettings = initProofSettings
            , theories = devTheories
            , currTheory = equivName
            , liveProofs = M.empty }

devTheories = foldl forceAddTheory noTheories $ devKnownBuiltins
forceAddTheory ths th 
  = case addTheory th ths of
      Yes ths' -> ths'
      But msgs -> error $ unlines' (thName th : msgs)

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
                    , ltlTheory
                    , arithmeticTheory
                    , setTheory
                    , listTheory
                    , utpWC_Theory
                    , utpNW_Theory
                    , designTheory
                    , utcpTheory
                    ]

\end{code}

\newpage
\subsection{Development Features}


\subsubsection{Listing Builtin Theories}

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

\subsubsection{Installing Builtin Theories}

\begin{code}
devInstallBuiltin :: REqState -> String -> IO (Maybe String,REqState)
devInstallBuiltin reqs thnm
  = case biLkp thnm devKnownBuiltins of
      Nothing
        -> return ( Just ("devInstallBuiltin: no builtin theory '"++thnm++"'")
                  , reqs)
      Just thry
        -> case addTheory thry $ theories reqs of
             But msgs -> return ( Just $ unlines' msgs,reqs )
             Yes thrys' -> return ( Nothing
                                  , changed reqs{ theories=thrys'
                                                , currTheory=thnm } )
\end{code}


\subsubsection{Resetting Existing Theory}

Only safe if the builtin version has the same dependency list
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
            case replaceTheory thnm thry0 thrys of
              But msgs   ->  return ( Just $ unlines' msgs, reqs )
              Yes thrys' ->  return ( Nothing, changed reqs{theories=thrys'} )
\end{code}

\newpage

\subsubsection{Updating Existing Theory}

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
