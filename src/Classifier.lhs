\section{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier where

data Direction 
    = Leftwards 
    | Rightwards 
    deriving (Eq,Show,Read)

data LawEntry 
    = String Direction 
    deriving (Eq,Show,Read)
    
type Simplifiers = [LawEntry]


\end{code}