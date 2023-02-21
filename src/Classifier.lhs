\section{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE RecordWildCards #-}
module Classifier where

import Laws

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

showSimpStr :: [(String, Direction)] -> String
showSimpStr (x:[]) = fst x
showSimpStr (x:xs) = fst x ++ showSimpStr xs

showAuto AutoLaws{..} =  "simps: "   ++ showSimpStr simps  ++ "\n"
                      ++ "folds: "   ++ concat folds       ++ "\n"
                      ++ "unfolds: " ++ concat unfolds     ++ "\n"

addLawsClassifier :: [Law] -> AutoLaws -> AutoLaws
addLawsClassifier lws au = au
\end{code}