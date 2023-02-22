\section{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE RecordWildCards #-}
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

showDir :: Direction -> String
showDir Leftwards  = "Leftwards"
showDir Rightwards = "Rightwards"

simpStr :: (String, Direction) -> String
simpStr sim = "(" ++ fst sim ++ "," ++ showDir (snd sim) ++ ")"

showSimps :: [(String, Direction)] -> String
showSimps (x:[]) = simpStr x
showSimps (x:xs) = simpStr x ++ showSimps xs

showAuto AutoLaws{..} =  "simps: "   ++ showSimps simps  ++ "\n"
                      ++ "folds: "   ++ concat folds       ++ "\n"
                      ++ "unfolds: " ++ concat unfolds     ++ "\n"

addLawsClassifier :: Term -> AutoLaws -> AutoLaws
addLawsClassifier te au = au
\end{code}