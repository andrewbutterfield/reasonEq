\section{Persistent Storage}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Persistence
  ( writeState
  , readState
  , persistentTest)
where

import System.Directory
import System.FilePath

import REqState
\end{code}

\subsection{File Paths}

\begin{code}
projectRoot   = "project"
projectExt    = "req"
projectFile   =  projectRoot <.> projectExt
pfile reqs = projectDir reqs ++ pathSeparator : projectFile
\end{code}

\subsection{Writing \reasonEq\ State}

\begin{code}
writeState :: REqState -> IO ()
writeState reqs
  = do let fp = pfile reqs
       writeFile fp $ unlines $ writeREqState reqs
\end{code}

\subsection{Reading \reasonEq\ State}

\begin{code}
readState :: FilePath -> IO REqState
readState fp
  = do txt <- readFile fp
       reqs <- readREqState $ lines txt
       return reqs{projectDir = projectDir reqs}
\end{code}

Mucking about:
\begin{code}
projectsList = "projects.txt"
currProject = "current.txt"

persistentTest :: IO ()
persistentTest
  = do fp <- getAppUserDataDirectory "req"
       putStrLn ("User Dir = "++fp)
       createDirectoryIfMissing True fp
       fps <- listDirectory fp
       putStrLn "Dir contents:"
       sequence_ $ map putStrLn fps
       plist <-
         if not (projectsList `elem` fps)
          then return []
          else do txt <- readFile projectsList
                  return $ lines txt
       putStrLn "Project Dirs:"
       sequence_ $ map putStrLn plist
       currp <-
         if not (currProject `elem` fps)
          then return Nothing
          else do txt <- readFile currProject
                  return $ Just txt
       putStrLn ("Current Project = " ++ show currp)
\end{code}
