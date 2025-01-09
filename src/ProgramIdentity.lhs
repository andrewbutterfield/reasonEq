\chapter{Program Identity}
\begin{verbatim}
Copyright (c) Andrew Butterfield 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module ProgramIdentity ( progName, progVersion, progNameVersion )
where

progName = "reasonEq"
progVersion = "0.9.1.0"
progNameVersion = progName++" "++progVersion
\end{code}