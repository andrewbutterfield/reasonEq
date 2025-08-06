\chapter{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023
           Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier 
  ( Direction(..)
  , AutoLaws(..)
  , nullAutoLaws, combineAutos, showAuto
  , addLawsClass
  , checkIsComp, checkIsSimp, checkIsFold, checkIsUnFold
  ) where

import qualified Data.Set as S
import Laws
import AST
import Assertions
import LexBase
import Proofs

import Debugger
\end{code}

\section{Classifier Declarations}

\subsection{Classifier Types}

\begin{code}
data Direction 
    = Leftwards 
    | Rightwards 
    deriving (Eq,Show,Read)

data AutoLaws = AutoLaws
  { simps    :: [(String, Direction)]
  , folds    :: [String]
  }
  deriving (Eq,Show,Read)
\end{code}

\newpage
\subsection{Classifier Top-Level Operations}
\begin{code}
nullAutoLaws
  = AutoLaws {  simps = []
             ,  folds = []
             }

combineTwoAuto :: AutoLaws -> AutoLaws -> AutoLaws
combineTwoAuto a b = AutoLaws {  simps = simps a ++ simps b
                              , folds = folds a ++ folds b
                              }

combineAutos :: AutoLaws -> [AutoLaws] -> AutoLaws
combineAutos auto [] = auto
combineAutos auto (x:xs) = combineAutos (combineTwoAuto auto x) xs
\end{code}

\subsection{Classifier Display}

\begin{code}
showDir :: Direction -> String
showDir Leftwards  = "Leftwards"
showDir Rightwards = "Rightwards"

simpStr :: (String, Direction) -> String
simpStr sim = "(" ++ fst sim ++ "," ++ showDir (snd sim) ++ ")"

showSimps :: [(String, Direction)] -> Int -> String
showSimps [] _ = ""
showSimps (x:[]) n = "\n\t" ++ show n ++ ". " ++ simpStr x
showSimps (x:xs) n = "\n\t" ++ show n ++ ". " 
                     ++ simpStr x ++ showSimps xs (n + 1)

showFolds :: [String] -> Int -> String
showFolds [] _ = ""
showFolds (x:[]) n = "\n\t" ++ show n ++ ". " ++ x
showFolds (x:xs) n = "\n\t" ++ show n ++ ". " ++ x ++ showFolds xs (n + 1)

showAuto alaws = "   i. simps:"  ++ showSimps (simps alaws) 1  ++ "\n\n"
              ++ "  ii. folds:"  ++ showFolds (folds alaws) 1  ++ "\n\n"
\end{code}

\section{Classifier Top Level}

\begin{code}
addLawClassifier :: NmdAssertion -> AutoLaws -> AutoLaws
addLawClassifier (nme, asser) au 
  = removeFoldSimps 
      $ AutoLaws { simps   = simps au   ++ addSimp nme (assnT asser)
                 , folds   = folds au   ++ addFold nme (assnT asser)
                 }
\end{code}

\begin{code}
addLawsClass :: [Law] -> AutoLaws -> AutoLaws
addLawsClass [] au = au 
addLawsClass (x:[]) au = (addLawClassifier (lawNamedAssn x) au)
addLawsClass (x:xs) au 
  = addLawsClass (xs) (addLawClassifier (lawNamedAssn x) au)
\end{code}


\section{Identify Simplifiers}

Given a law $P \equiv Q$ (or $e = f$),
we compare the sizes of $P$ and $Q$.
If $P$ is larger that $Q$, 
then using the law left-to-right is a simplification.
If $Q$ is larger, then right-to-left simplifies.
For now any size difference at all is used to classify laws.
A possible future modification might require a size difference threshold.
\begin{code}
addSimp :: String -> Term -> [(String, Direction)]
addSimp nme (Cons _ _ (Identifier "eqv" 0) (p:q:[]))
  = checkSimp nme p q
addSimp nme (Cons _ _ (Identifier "eq" 0) (e:f:[]))
  = checkSimp nme e f
addSimp _ _ = []

checkSimp nme p q
  = do  let sizeP = termSize p
        let sizeQ = termSize q
        if sizeP > sizeQ
          then [(nme, Leftwards)] 
        else if sizeP < sizeQ
          then [(nme, Rightwards)]
        else []
\end{code}


\section{Identify Folds}

\begin{code}
addFold :: String -> Term -> [(String)]
addFold nme (Cons _ sb (Identifier "eqv" 0) (p:q:[])) 
  =  if isFold p
     then if checkQ q (getN p)
          then [nme] 
          else []
     else []
addFold nme _ = []
\end{code}

\begin{code}
isFold :: Term -> Bool
isFold (Cons _ _ _ xs@(_:_))
            | all isVar xs && allUnique xs = True
            | otherwise = False
isFold _ = False

allUnique :: (Eq a) => [a] -> Bool
allUnique []     = True
allUnique (x:xs) = x `notElem` xs && allUnique xs

getN :: Term -> Identifier
getN (Cons _ _ n _) = n

checkQ :: Term -> Identifier -> Bool
checkQ (Cons _ _ n _) i  =  n /= i
checkQ _ _ = True
\end{code}

Exported only:
\begin{code}
checkIsSimp :: (String, Direction) -> MatchClass -> Bool
checkIsSimp (_, Rightwards) MatchEqvRHS = True
checkIsSimp (_, Leftwards) MatchEqvLHS = True
checkIsSimp _ _ = False

checkIsComp :: (String, Direction) -> MatchClass -> Bool
checkIsComp (_, Rightwards) MatchEqvLHS = True
checkIsComp (_, Leftwards) MatchEqvRHS = True
checkIsComp (_, _) (MatchEqvVar _) = True
checkIsComp _ _ = False

checkIsFold :: MatchClass -> Bool
checkIsFold  MatchEqvRHS = True
checkIsFold  MatchEqvLHS = False
checkIsFold  _ = False

checkIsUnFold :: MatchClass -> Bool
checkIsUnFold MatchEqvLHS = True
checkIsUnFold MatchEqvRHS = False
checkIsUnFold _ = False 
\end{code}

\section{Remove Fold Simplifiers}

\begin{code}
removeFoldSimps :: AutoLaws -> AutoLaws
removeFoldSimps au 
  = AutoLaws { simps = removeSimpsList (folds au) (simps au)
             , folds = folds au
             }

removeSimpsList :: [String] -> [(String, Direction)] -> [(String, Direction)]
removeSimpsList [] ys = ys
removeSimpsList (x:xs) ys = removeSimpsList xs $ removeSimp x ys

removeSimp :: String -> [(String, Direction)] -> [(String, Direction)]
removeSimp _ [] = []
removeSimp x (y:ys) | x == fst y    = removeSimp x ys
                    | otherwise = y : removeSimp x ys
\end{code}

