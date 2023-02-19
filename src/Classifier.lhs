\section{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier where

import Laws

data Direction 
    = Leftwards 
    | Rightwards 
    deriving (Eq,Show,Read)

data LawEntry 
    = String Direction 
    deriving (Eq,Show,Read)

addLawsClassifier :: [Law] -> [LawEntry] -> [LawEntry]
addLawsClassifier lws clss = clss
\end{code}