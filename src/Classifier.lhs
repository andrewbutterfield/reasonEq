\section{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier where

import Laws
import AST

data Direction 
    = Leftwards 
    | Rightwards 
    deriving (Eq,Show,Read)

data AutoLaws = AutoLaws
  { simps    :: [(String, Direction)]
  , folds    :: [String]
  , unfolds  :: [String]
  }
  deriving (Eq,Show,Read)

nullAutoLaws
  = AutoLaws {  simps = []
             ,  folds = []
             ,  unfolds = []
             }

showDir :: Direction -> String
showDir Leftwards  = "Leftwards"
showDir Rightwards = "Rightwards"

simpStr :: (String, Direction) -> String
simpStr sim = "(" ++ fst sim ++ "," ++ showDir (snd sim) ++ ")"

showSimps :: [(String, Direction)] -> String
showSimps [] = ""
showSimps (x:[]) = simpStr x
showSimps (x:xs) = simpStr x ++ showSimps xs

showAuto alaws = "   1. simps   -> "   ++ showSimps (simps alaws)  ++ "\n"
              ++ "   2. folds   -> "   ++ concat (folds alaws)     ++ "\n"
              ++ "   3. unfolds -> "   ++ concat (unfolds alaws)    ++ "\n"

addLawsClassifier :: Term -> AutoLaws -> AutoLaws
addLawsClassifier te au = au
\end{code}