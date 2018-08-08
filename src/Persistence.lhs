\section{Persistent Storage}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Persistence
  ( writeState
  , readState
  , writeNamedTheory
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
projectPath projDir = projDir ++ pathSeparator : projectFile
pfile reqs = projectPath $ projectDir reqs
tfile pjdir nm = pjdir ++ pathSeparator : nm <.> projectExt
\end{code}

\subsection{Writing \reasonEq\ State}

\begin{code}
writeState :: REqState -> IO ()
writeState reqs
  = do let (tsTxt,nTsTxts) = writeREqState reqs
       let fp = pfile reqs
       writeFile fp $ unlines tsTxt
       sequence_ $ map (writeNamedTheory reqs) nTsTxts

writeNamedTheory reqs (nm,thTxt)
  = do let fp = tfile (projectDir reqs) nm
       writeFile fp $ unlines thTxt
\end{code}

\subsection{Reading \reasonEq\ State}

\begin{code}
readState :: FilePath -> IO REqState
readState projfp
  = do txt  <- readFile $ projectPath projfp
       ((sig,thnms),rest1) <- readREqState1 $ lines txt
       nmdThrys <- sequence $ map (readNamedTheory projfp) thnms
       reqs <- readREqState2 sig nmdThrys rest1
       return reqs{projectDir = projfp}

readNamedTheory projfp nm
  = do let fp = tfile projfp nm
       txt <- readFile fp
       (thry,rest) <- readTheory $ lines txt
       return (nm,thry)
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
