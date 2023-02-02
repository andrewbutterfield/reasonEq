\section{File Handling}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Files 
  ( projectName, projectExt
  , getWorkspaces
  , currentWorkspace
  )
where

import System.Directory
import System.FilePath
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
getWorkspaces :: String -> IO (FilePath, [String])
getWorkspaces appname
 = do userAppPath <- getAppUserDataDirectory appname
      exists <- doesDirectoryExist userAppPath
      if exists
      then getAllWorkspaces userAppPath
      else do createUserAppDir userAppPath
              getAllWorkspaces userAppPath
\end{code}

Useful names, markers and separators:
\begin{code}
wsRoot = "workspaces.wsp"
defProjName = "MyReasonEq"
currentMarker = '*'
pathSep = '|'
\end{code}

First time we run \reasonEq, we need to setup user data.
\begin{code}
createUserAppDir dirpath
  = do putStrLn ("Creating app. dir.: "++dirpath)
       createDirectory dirpath
       currDir <- getCurrentDirectory
       let deffp = currDir </> defProjName
       putStrLn ("Creating workspace : "++deffp)
       writeFile (dirpath </> wsRoot)
        $ unlines
            [ currentMarker:defProjName ++ pathSep:deffp ]
\end{code}

Get all known workspaces from user data.
\begin{code}
getAllWorkspaces :: FilePath -> IO (FilePath, [String])
getAllWorkspaces dirpath
 = do projTxt <- readFile (dirpath </> wsRoot)
      let projDescrs = lines projTxt
      return (dirpath, lines projTxt)
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
                 -> [String] -- workspace listing
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
findCurrent (ln:lns)
 | take 1 ln == [currentMarker] = return (nm,fp)
 | otherwise                    = findCurrent lns
 where
   (nm,after) = break (==pathSep) $ drop 1 ln
   fp = drop 1 after
\end{code}
