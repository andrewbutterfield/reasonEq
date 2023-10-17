\section{Persistent Storage}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--21

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Persistence
  ( writeAllState, readAllState
  , writeNamedTheory, readNamedTheory
  , writeConjectures, readFiledConjectures
  , writeProof, readProof
  )
where

import System.Directory
import System.FilePath

import Utilities
import Control
import Files
import REqState

import Debugger
\end{code}

\subsection{Persistent \reasonEq\ State}

In the project directory we have a top-level file called \texttt{project.req}
that holds overall data regarding the project.
\begin{code}
projectPath projDir = projDir </> projectName <.> projectExt
\end{code}

\begin{code}
writeAllState :: REqState -> IO REqState
writeAllState reqs
  = do let pjdir = projectDir reqs
       mifte (doesDirectoryExist pjdir)
         (doWriteAll reqs pjdir)
         (noSuchDirectory reqs pjdir)
  where
    doWriteAll reqs pjdir
      = do  let (tsTxt,nTsTxts) = writeREqState reqs
            let fp = projectPath pjdir
            writeFile fp $ unlines tsTxt
            sequence_ $ map (writeNamedTheoryTxt pjdir) nTsTxts
            putStrLn ("REQ-STATE written to '"++projectDir reqs++"'.")
            return reqs{ modified = False }
\end{code}
       
       


\begin{code}
readAllState :: REqState -> FilePath -> IO REqState
readAllState reqs projdirfp
  = mifte (doesDirectoryExist projdirfp)
      (doReadAll projdirfp)
      (noSuchDirectory reqs projdirfp)
  where
    doReadAll projdirfp
      = do  let projfp = projectPath projdirfp
            txt <- readFile projfp
            ((settings,thnms),rest1) <- readREqState1 $ lines txt
            nmdThrys <- sequence 
                        $ map (readNamedTheory projdirfp) thnms
            newreqs <- readREqState2 settings nmdThrys rest1
            putStrLn ("Read project details from "++projfp)
            return newreqs{projectDir = projdirfp}
\end{code}


\subsection{Persistent Theory}

We also have files called \texttt{<thryName>.thr}
for every theory called $\langle thryName\rangle$.
\begin{code}
theoryExt      =  "thr"
theoryPath projDir thname = projDir </> thname <.> theoryExt
\end{code}


\begin{code}
writeNamedTheory :: FilePath -> (FilePath, Theory) -> IO ()
writeNamedTheory pjdir (nm,theory)
  = do let fp = theoryPath pjdir nm
       writeFile fp $ unlines $ writeTheory theory
\end{code}

\begin{code}
writeNamedTheoryTxt :: FilePath -> (FilePath, [String]) -> IO ()
writeNamedTheoryTxt pjdir (nm,thTxt)
  = do let fp = theoryPath pjdir nm
       writeFile fp $ unlines thTxt
\end{code}

\begin{code}
readNamedTheory :: String -> String -> IO ([Char], Theory)
readNamedTheory projfp nm
  = do let fp = theoryPath projfp nm
       txt <- readFile fp
       (thry,rest) <- readTheory $ lines txt
       putStrLn ("Read theory '"++nm++"'")
       return (nm,thry)
\end{code}

\newpage
\subsection{Persistent Conjecture}

For conjecture files, we use the extension \texttt{.cnj}.
\begin{code}
conjExt = "cnj"
conjPath projDir conjName = projDir </> conjName <.> conjExt
\end{code}

\begin{code}
writeConjectures :: Show a => REqState -> String -> [a] -> IO ()
writeConjectures reqs nm conjs
  = do let fp = conjPath (projectDir reqs) nm
       writeFile fp $ unlines $ map show conjs
\end{code}

\begin{code}
readFiledConjectures :: FilePath -> String -> IO [NmdAssertion]
readFiledConjectures projfp nm
  = do let fp = conjPath projfp nm
       txt <- readFile fp
       return $ readShown $ lines txt

readShown [] = []
readShown (ln:lns)
 | null (trim ln) = readShown lns
 | otherwise      = (read ln) : readShown lns
\end{code}

\subsection{Persistent Proof}

For proof files, we use the extension \texttt{.prf}.
\begin{code}
proofExt = "prf"
proofPath projDir proofName = projDir </> proofName <.> proofExt
\end{code}

\begin{code}
writeProof :: REqState -> String -> Proof -> IO ()
writeProof reqs nm proof
  = do let fp = proofPath (projectDir reqs) nm
       writeFile fp $ show proof
\end{code}

\begin{code}
readProof :: FilePath -> String -> IO (Maybe Proof)
readProof projfp nm
  = do let fp = proofPath projfp nm
       fileExists <- doesFileExist fp
       if fileExists
       then  do  txt <- readFile fp
                 return $ Just $ read txt
                 -- SHOULD REALLY CHECK PROOF NAME AGAINST FILENAME
       else  do  putStrLn ("Proof file '"++fp++"' not found.")
                 return Nothing
\end{code}

\subsection{Error Reporting}

\begin{code}
noSuchDirectory reqs pjdir
  = do  putStrLn ("Directory "++pjdir++" does not exist")
        return reqs       
\end{code}


