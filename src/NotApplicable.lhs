\section{Not Applicable Datatype}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module NotApplicable (
  NA(..)
)
where
\end{code}

This is a type (isomorphic to \h{Maybe}) that indicates
when a component is not relevant/applicable in some analysis.

\subsection{Datatype: The, NA}

\begin{code}
data NA t
 = NA
 | The t
 deriving (Eq,Ord,Show,Read)
\end{code}

\subsection{Instances}

\begin{code}
instance Functor NA where
  fmap f (The x)    =  The $ f x
  fmap f NA         =  NA
\end{code}
