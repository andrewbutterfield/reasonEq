\section{Persistent Storage}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Persistence
  ( writeAllState
  , readAllState
  , writeNamedTheoryTxt
  , readNamedTheory
  , writeConjectures
  , readFiledConjectures
  )
where

import System.Directory
import System.FilePath

import Utilities
import REqState
\end{code}

\subsection{File Paths}

In the project directory we have a top-level file called \texttt{project.req}
that holds overall data regarding the project.
\begin{code}
projectRoot   = "project"
projectExt    = "req"
projectFile   =  projectRoot <.> projectExt
projectPath projDir = projDir ++ pathSeparator : projectFile
pfile reqs = projectPath $ projectDir reqs
\end{code}
We also have files called \texttt{<thryName>.thr}
for every theory called $\langle thryName\rangle$.
\begin{code}
theoryExt      =  "thr"
tfile pjdir nm = pjdir ++ pathSeparator : nm <.> theoryExt
\end{code}
For conjecture files, we use the extension \texttt{.cnj}.
\begin{code}
conjectureExt = "cnj"
cjfile pjdir nm = pjdir ++ pathSeparator : nm <.> conjectureExt
\end{code}

\subsection{Persistent \reasonEq\ State}

\begin{code}
writeAllState :: REqState -> IO ()
writeAllState reqs
  = do let (tsTxt,nTsTxts) = writeREqState reqs
       let fp = pfile reqs
       writeFile fp $ unlines tsTxt
       sequence_ $ map (writeNamedTheoryTxt reqs) nTsTxts
\end{code}

\begin{code}
readAllState :: FilePath -> IO REqState
readAllState projfp
  = do txt  <- readFile $ projectPath projfp
       ((sets,sig,thnms),rest1) <- readREqState1 $ lines txt
       nmdThrys <- sequence $ map (readNamedTheory projfp) thnms
       reqs <- readREqState2 sets sig nmdThrys rest1
       return reqs{projectDir = projfp}
\end{code}


\subsection{Persistent Theory}

\begin{code}
writeNamedTheoryTxt reqs (nm,thTxt)
  = do let fp = tfile (projectDir reqs) nm
       writeFile fp $ unlines thTxt
\end{code}

\begin{code}
readNamedTheory projfp nm
  = do let fp = tfile projfp nm
       txt <- readFile fp
       (thry,rest) <- readTheory $ lines txt
       return (nm,thry)
\end{code}

\subsection{Persistent Conjecture}

\begin{code}
writeConjectures reqs nm conjs
  = do let fp = cjfile (projectDir reqs) nm
       writeFile fp $ unlines $ map show conjs
\end{code}

\begin{code}
readFiledConjectures :: FilePath -> String -> IO [NmdAssertion]
readFiledConjectures projfp nm
  = do let fp = cjfile projfp nm
       txt <- readFile fp
       return $ readShown $ lines txt

readShown [] = []
readShown (ln:lns)
 | null (trim ln) = readShown lns
 | otherwise      = (read ln) : readShown lns
\end{code}
