\section{Utilities}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Utilities
where

import Data.List
\end{code}

Here we provide odds and ends not found elswhere.

\subsection{List Functions}

\subsubsection{Predicate: has duplicates}
\begin{code}
hasdup :: Eq a => [a] -> Bool
hasdup xs = xs /= nub xs
\end{code}

\subsection{Possible Failure Monad}

\subsubsection{Datatype: Yes, But \dots}

\begin{code}
data YesBut t
 = Yes t
 | But String
 deriving (Eq,Show)
\end{code}

\subsubsection{Instances: Functor, Applicative, Monad}

\begin{code}
instance Functor YesBut where
  fmap f (Yes x)    =  Yes $ f x
  fmap f (But msg)  =  But msg

instance Applicative YesBut where
  pure x = Yes x

  Yes f <*> Yes x    =  Yes $ f x
  Yes f <*> But msg  =  But msg
  But msg <*> _      =  But msg

instance Monad YesBut where
  Yes x   >>= f   =  f x
  But msg >>= f   =  But msg

  fail msg        =  But msg
\end{code}
