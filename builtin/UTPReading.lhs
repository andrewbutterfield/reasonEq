\chapter{UTP Reading}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTPReading (
  bookdef
) where

import AST
import SideCond
import Laws
import StdSignature
\end{code}


\section{Introduction}

Code to generate a reference to the literature.

We want to map definition and law numbers
from the a document to law names.
\begin{code}
bookdef :: String -> String -> Term -> SideCond
        -> (NmdAssertion, (String, String))
bookdef name alias prop sc
  = (preddef name prop sc,(alias,name))
\end{code}

