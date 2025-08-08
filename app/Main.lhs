\chapter{Main Program}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2017--24
              Saqid Zardari     2023
              Aaron Bruce       2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.Environment
import System.IO
import System.FilePath
import System.Directory
import System.Exit
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char

import Symbols hiding (help)

import YesBut
import Utilities
import StratifiedDAG
import Persistence

import ProgramIdentity
import LexBase
import Variables
import AST
import VarData
import Binding
import Typing
import SideCond
import Assertions
import Ranking
import REqState
import UI.AbstractUI
import Instantiate
import TestRendering
import Parsing
import Dev
import SAT
import Classifier
import LiveProofs
import UI.REPL
import UI.ProverTUI
import UI.TopTUI

import Debugger
\end{code}

\newpage

\section{\texttt{main}}

The program takes command-line arguments
that tailor its behaviour.
For now, we consider the following behavioural aspects:
\begin{description}
  \item [UI]
    We propose to support both a text-based REPL
    and a graphical user-interface. The REPL is the default,
    while the GUI can be invoked with the \texttt{-g} argument (anywhere).
  \item [FS]
    We allow the specification of where in the filesystem the prover data files
    are kept.
    We support a project-based approach, where a project is simply
    a folder (``workspace'') containing all relevant files.
    We can specify the path to same using the \texttt{-w} command-line option.
    We also have the notion of a single separate folder with global data
    that gives the locations of all known project folders.
    For now this lives in a OS-dependent user-specific location.
    In particular we use a design that allows the program itself
    to setup global configuration data, in an OS-dependent manner.
  \item [Dev]
    We also allow two modes when running: ``User'' \texttt{-u}
    and ``Dev'' \texttt{-d}.
    In User mode, the default, all prover state is loaded from data files,
    as specified by FS above.
    In Dev mode, some prover state may be pre-installed,
    and there may be additional proof commands available.
\end{description}

So we can summarise flags as follows:
\begin{code}
helpFlag        = "-h"
helpLongFlag    = "--help"
versionFlag     = "-v"
versionLongFlag = "--version"

guiFlag        = "-g"    --          use GUI
replFlag       = "-r"    --          use REPL (default)
workspaceFlag  = "-w"    -- <path>   path to prover workspace
userFlag       = "-u"    --          run in 'User' mode
devFlag        = "-d"    --          run in 'Dev' mode
cwdConfig      = ".req"  -- local config file (contains flags)

helpinfo
 = putStrLn $ unlines
     [ "Usage:\n"
     , "req [command-line-options]\n"
--     , option guiFlag "start-up GUI"
     , option replFlag "start-up REPL"
     , option (workspaceFlag++" <dir>") "workspace directory"
     , option userFlag "start-up in User mode (default)"
     , option devFlag "start-up in Dev mode"
     , ""
     , "\t-h, --help \t output this help and exit"
     , "\t-v, --version \t output program version and exit"
--     , ""
--     , "options can also be included in file '.req'"
     ]
 where
   option flag explanation = '\t':flag ++ '\t':explanation
\end{code}

\newpage
We shall define a record to record flag data,
and a corresponding parser:
\begin{code}
data CMDFlags = CMDFlags { usegui  :: Bool
                         , wspath :: Maybe FilePath
                         , dev     :: Bool}

defFlags = CMDFlags { usegui  = False
                    , wspath = Nothing
                    , dev     = False }

parseArgs :: [[Char]] -> CMDFlags
parseArgs args = parse defFlags args where
  parse flags [] = flags
  parse flags (f:p:ss)
   | f == workspaceFlag  =  parse flags{ wspath = checkfp p } ss
   where checkfp fp
           | isValid fp  =  Just fp
           | otherwise   =  Nothing
  parse flags (f:ss)
   | f == guiFlag      =  parse flags{ usegui = True  }   ss
   | f == replFlag     =  parse flags{ usegui = False }   ss
   | f == userFlag     =  parse flags{ dev    = False }   ss
   | f == devFlag      =  parse flags{ dev    = True  }   ss
   -- ignore anything else
   | otherwise         =  parse flags                     ss
\end{code}

\begin{code}
main :: IO ()
main
  = do args <- getArgs
       info args runargs

info args runargs
 | args == [helpFlag]         =  helpinfo
 | args == [helpLongFlag]     =  helpinfo
 | args == [versionFlag]      =  putStrLn progNameVersion
 | args == [versionLongFlag]  =  putStrLn progNameVersion
 | otherwise                  =  runargs args

runargs args
  = do let flags = parseArgs args
       reqs0 <- initState flags
       if usegui flags
       then do putStrLn "starting GUI..."
               gui reqs0
       else do putStrLn "starting REPL..."
               tui reqs0
\end{code}


\newpage
\section{Initialising State}

We assume user mode by default.

\begin{code}
initState :: CMDFlags -> IO REqState

initState flags
  = case wspath flags of
      Nothing ->
        if dev flags
        then return $ devInitState
        else do  putStrLn "Running user mode, default initial state."
                 (appFP,projects) <- getWorkspaces progName
                 putStrLn ("appFP = "++appFP)
                 putStrLn ("projects:\n"++(unlines $ map show projects))
                 (ok,pname,projfp) <- currentWorkspace projects
                 putStrLn ("Project Name: "++pname)
                 putStrLn ("Project Path: "++projfp)
                 putStrLn "Loading..."
                 loadAllState reqstate0 projfp
      Just fp ->
        do ok <- doesDirectoryExist fp
           if ok
           then if dev flags
                then return $ devInitState{ projectDir = fp }
                else do putStrLn "Running user mode, loading project state."
                        loadAllState reqstate0 fp
           else die ("invalid workspace: "++fp)
\end{code}

\newpage


\section{GUI Top-Level}

The GUI has yet to be developed but will probably
use \texttt{threepenny-gui} along with the Electron browser.
\begin{code}
gui :: REqState -> IO ()
gui reqs0 = do putStrLn "GUI not implemented, using command-line."
               tui reqs0
\end{code}

