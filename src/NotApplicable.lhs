\section{Not Applicable Datatype}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module NotApplicable (
  NA(..), isNA, isThe, the
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

\subsection{Queries}

\begin{code}
isNa, isThe :: NA t -> Bool 
isNA NA  = True  ; isNA (The _)  = False
isThe NA = False ; isThe (The _) = True

the :: NA t -> t  -- partial function
the NA       =  error "the: applied to NA"
the (The t)  =  t
\end{code}
