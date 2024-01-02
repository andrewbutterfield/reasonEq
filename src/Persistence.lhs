\section{Persistent Storage}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--21

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Persistence
  ( projectName, projectExt
  , getWorkspaces
  , currentWorkspace
  , ifDirectoryExists, ifFileExists
  , writeAllState, readAllState
  , writeNamedTheory, readNamedTheory
  , writeConjectures, readFiledConjectures
  , writeProof, readProof
  )
where

import System.Directory
import System.FilePath

import Utilities
import YesBut
import Control
import REqState

import Debugger
\end{code}

\subsection{Startup}

We check first for the existence of the ``user application''
directory. If it exists, then we use its contents
to identify the workspace and load up the prover state.
If not present, we assume this is the first time running,
so we create it, and create a default workspace
in the current working directory.


\subsection{User Application Directory}

We return the path of the user application directory,
plus the contents of its workspaces file.

\begin{code}
type WorkSpace = ( Bool -- True if the current workspace
                 , String -- workspace name
                 , String -- path to workspace 
                 )
getWorkspaces :: String -> IO (FilePath, [WorkSpace])
getWorkspaces appname
 = do userAppPath <- getAppUserDataDirectory appname
      mifte (doesDirectoryExist userAppPath)
            (getAllWorkspaces userAppPath)
            (do createUserAppDir userAppPath
                getAllWorkspaces userAppPath)
\end{code}

Useful names, markers and separators:
\begin{code}
wsRoot = "workspaces.wsp"
defaultProjectName = "MyReasonEq"
currentMarker = '*'
pathSep = '|'
\end{code}

First time we run \reasonEq, we need to setup user data.
\begin{code}
createUserAppDir dirpath
  = do putStrLn ("Creating app. dir.: "++dirpath)
       createDirectory dirpath
       currDir <- getCurrentDirectory
       let deffp = currDir </> defaultProjectName
       putStrLn ("Creating workspace : "++deffp)
       writeFile (dirpath </> wsRoot)
        $ unlines
            [ currentMarker:defaultProjectName ++ pathSep:deffp ]
\end{code}

Get all known workspaces from user data.
\begin{code}
getAllWorkspaces :: FilePath -> IO (FilePath, [WorkSpace])
getAllWorkspaces dirpath
 = let wsfp = dirpath </> wsRoot
   in ifFileExists "Workspace" ("",[]) wsfp (doGetWS wsfp)
 where
   doGetWS wsfp = do projTxt <- readFile wsfp
                     wsps <- parseWorkspaces $ lines projTxt
                     return (dirpath, wsps)

parseWorkspaces :: [String] -> IO [WorkSpace]
parseWorkspaces lns = parseWSs [] lns
parseWSs ssw [] = return $ reverse ssw
parseWSs ssw (ln:lns)
  =  case parseWorkspace ln of
       But msgs  ->  do  putStrLn $ unlines' msgs
                         parseWSs ssw lns
       Yes ws    ->  parseWSs (ws:ssw) lns 

parseWorkspace :: MonadFail mf => String -> mf WorkSpace
parseWorkspace ln
 | take 1 ln == [currentMarker]  =  parseNameAndPath True  $ drop 1 ln
 | otherwise                     =  parseNameAndPath False ln
 
parseNameAndPath isCurrent ln
  | null nm    =  fail ("parseWorkspace - no name: "++ln)
  | null fp    =  fail ("parseWorkspace - no filepath: "++ln)
  | otherwise  =  return (isCurrent,nm,fp)
  where
    (nm,after)  =  break (==pathSep) ln
    fp          =  drop 1 after
\end{code}

\newpage
\subsection{Current Workspace}

The project/workspace master file:
\begin{code}
projectName = "project"
projectExt = "req"
projectFile =  projectName <.> projectExt
\end{code}

We lookup the current workspace.
If it exists, we check for the project file,
and complain if that does not exist.
If the current workspace does not exist,
we create it, and initialise the project file.
\begin{code}
currentWorkspace :: String -- initial project file contents
                 -> [WorkSpace] -- workspace listing
                 -> IO (String,FilePath)
currentWorkspace defReqState []
  = error ("No workspaces defined - ")

currentWorkspace defReqState wsSpecs
  = case findCurrent wsSpecs of
      Nothing -> error "No current workspace!"
      Just (currNm, currFP) ->
        do dirExists <- doesDirectoryExist currFP
           let projFP = currFP </> projectFile
           if dirExists
           then do fileExists <- doesFileExist projFP
                   if fileExists
                   then return (currNm,currFP)
                   else fail ("Missing file: "++projFP )
           else do putStrLn ("Creating "++currFP)
                   createDirectory currFP
                   putStrLn ("Creating "++projFP)
                   writeFile projFP defReqState
                   return (currNm,currFP)
\end{code}

Look for the workspace marked as current:
\begin{code}
findCurrent [] = fail "No current workspace!"
findCurrent ((True,nm,fp):_) = return (nm,fp)
findCurrent (_:wss) = findCurrent wss
\end{code}

\subsection{Error Reporting}

\begin{code}
noSuchDirectory :: String -> a -> FilePath -> IO a
noSuchDirectory what junk dir
  = do  putStrLn (what++" Directory "++dir++" does not exist")
        return junk       
\end{code}

\begin{code}
ifDirectoryExists :: String -> a -> FilePath -> IO a -> IO a
ifDirectoryExists what junk dir useDirectory
  = mifte (doesDirectoryExist dir) 
          useDirectory
          (noSuchDirectory what junk dir)      
\end{code}

\begin{code}
noSuchFile :: String -> a -> FilePath -> IO a
noSuchFile what junk file
  = do  putStrLn (what++" File "++file++" does not exist")
        return junk       
\end{code}

\begin{code}
ifFileExists :: String -> a -> FilePath -> IO a -> IO a
ifFileExists what junk file useFile
  = mifte (doesFileExist file) 
          useFile
          (noSuchFile what junk file)      
\end{code}


\newpage
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
       ifDirectoryExists "REQ-STATE" reqs pjdir (doWriteAll reqs pjdir)
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
  = ifDirectoryExists "REQ-STATE" reqs projdirfp (doReadAll projdirfp)
  where
    doReadAll projdirfp
      = do  let projfp = projectPath projdirfp
            txt <- readFile projfp
            ((settings,thnms),rest1) <- readREqState1 $ lines txt
            nmdThrys <- getNamedTheories projdirfp thnms
            newreqs <- readREqState2 settings nmdThrys rest1
            putStrLn ("Read project details from "++projfp)
            return newreqs{projectDir = projdirfp}

getNamedTheories projfp nms
  = ifDirectoryExists "Theories" [] projfp (getNamedTheories' projfp nms)

-- assumes that projfp exists
getNamedTheories' _ [] = return []
getNamedTheories' projfp (nm:nms)
  = let fp = theoryPath projfp nm
    in ifFileExists "Theory" [] fp (doGetNamedTheories projfp fp nm nms)
  where
    doGetNamedTheories projfp fp nm nms
      =  do nmdThry <- getNamedTheory fp nm
            nmdThrys <- getNamedTheories' projfp nms
            return (nmdThry:nmdThrys)
\end{code}

\newpage
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
  = ifDirectoryExists "Theory" () pjdir (doWriteTheory pjdir nm theory)
  where
    doWriteTheory pjdir nm theory 
      =  do let fp = theoryPath pjdir nm
            writeFile fp $ unlines $ writeTheory theory
            putStrLn ("Theory '"++nm++"' written to '"++pjdir++"'.")
\end{code}

\begin{code}
writeNamedTheoryTxt :: FilePath -> (FilePath, [String]) -> IO ()
writeNamedTheoryTxt pjdir (nm,thTxt)
  = ifDirectoryExists "Theory" () pjdir (doWriteTheoryTxt pjdir nm thTxt)
  where
    doWriteTheoryTxt pjdir nm thTxt
      = do  let fp = theoryPath pjdir nm
            writeFile fp $ unlines thTxt
            putStrLn ("Theory '"++nm++"' written to '"++pjdir++"'.")
\end{code}

\begin{code}
readNamedTheory :: Theories -> String -> String -> IO (Bool,Bool,Theories)
readNamedTheory thrys projfp nm
  = let fp = theoryPath projfp nm
    in ifFileExists "Theory" (False,False,undefined) 
                    fp (doReadNamedTheory thrys fp nm)
  where
    doReadNamedTheory thrys fp nm
      = do  (nm,thry) <- getNamedTheory fp nm
            let isOld = nm `isATheoryIn` thrys
            let thrys' = ( if isOld
                           then replaceTheory' thry thrys
                           else addTheory' thry thrys )
            if isOld 
              then putStrLn ("Theory '"++nm++"' already exists")
              else return ()
            return (True,isOld,thrys')

-- assumes fp exists
getNamedTheory :: String -> String -> IO (String,Theory)
getNamedTheory fp nm 
  = do  txt <- readFile fp
        (thry,_) <- readTheory $ lines txt
        putStrLn ("Read theory '"++nm++"' from "++fp)
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
  = let projfp = projectDir reqs
    in ifDirectoryExists "Conjecture" () projfp 
       (doWriteConjs projfp nm conjs)
  where
    doWriteConjs projfp nm conjs
      = do let fp = conjPath projfp nm
           writeFile fp $ unlines $ map show conjs
           return ()
\end{code}

\begin{code}
readFiledConjectures :: FilePath -> String -> IO [NmdAssertion]
readFiledConjectures projfp nm
  = let fp = conjPath projfp nm
    in ifFileExists "Conjecture" [] fp (doReadFiledConj fp)
  where
    doReadFiledConj fp
      =  do  txt <- readFile fp
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
  = let fp = proofPath (projectDir reqs) nm
    in ifFileExists "Proof" () fp (writeFile fp $ show proof)
\end{code}

\begin{code}
readProof :: FilePath -> String -> IO (Maybe Proof)
readProof projfp nm
  = let fp = proofPath projfp nm
    in ifFileExists "Proof" Nothing fp (doReadProof fp nm)
  where
    doReadProof fp nm
      =  do txt <- readFile fp
            return $ Just $ read txt
            -- SHOULD REALLY CHECK PROOF NAME AGAINST FILENAME
\end{code}


