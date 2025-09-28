\chapter{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023
           Andrew Butterfield (c) 2024--25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier 
  ( Direction(..), AutoLaws(..), nullAutoLaws, showAuto
  , combineAutos
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

nullAutoLaws  = AutoLaws { simps = [], folds = [] }
\end{code}

\newpage
\subsection{Classifier Top-Level Operations}
\begin{code}
combineTwoAuto :: AutoLaws -> AutoLaws -> AutoLaws
combineTwoAuto a b = AutoLaws {  simps = simps a ++ simps b
                              , folds = folds a ++ folds b
                              }

combineAutos :: [AutoLaws] -> AutoLaws
combineAutos [] = nullAutoLaws
combineAutos (alws:alwss) = combineTwoAuto alws (combineAutos alwss)
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
addLawClassifier :: Law -> AutoLaws -> AutoLaws
addLawClassifier ((nme, assn),provenance) au 
  = reconcileFoldSimps 
      $ AutoLaws { simps   = simps au   ++ addSimp nme (assnT assn)
                 , folds   = folds au   ++ addFold nme (assnT assn)
                 }
\end{code}

\begin{code}
addLawsClass :: [Law] -> AutoLaws -> AutoLaws
addLawsClass [] au = au 
addLawsClass (x:[]) au = (addLawClassifier x au)
addLawsClass (x:xs) au 
  = addLawsClass (xs) (addLawClassifier x au)
\end{code}


\section{Identify Simplifiers}

Given a law $P \equiv Q$ (or $e = f$),
we compare the sizes of $P$ and $Q$.
If $P$ is larger that $Q$, 
then using the law left-to-right is a simplification.
If $Q$ is larger, then right-to-left simplifies.
For now any size difference at all is used to classify laws.
\textbf{
A possible future modification might require a size difference threshold.
This could also be based on either absolute or relative differences.
It might make sense for this to be a setting at the level of individual theories.
}
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

\section{Reconcile Folds and  Simplifiers}

Many definitions have the same shape as a 
(typically right-to-left) simplifier.
We want any classified law to only have one classification,
so we usually decide they are classified as definitions,
and not simplifiers.
However, some logical operators satisfy a number of laws,
each of which satisfies the requirements to be a definition.
For example, logical implication satisfies the following laws:
\begin{eqnarray*}
   P \implies Q &\equiv& \lnot P \lor Q
\\ P \implies Q &\equiv& (P \land Q \equiv P)
\\ P \implies Q &\equiv& (P \lor Q \equiv Q)
\end{eqnarray*}
The first is a commonly used definition,
while the second is used in \cite{gries.93}.
The second and third capture the fact 
that implication is an complete lattice ordering.


Right now, all three lasws above are classified as definitions,
and  ``reconciliation'' just removes simplification status
from anything judged to be a definition.
What we need to do is to let the one used as an axiom be the definition,
while the other get classified as simplifiers.
\begin{code}
-- needs rework!
reconcileFoldSimps :: AutoLaws -> AutoLaws
reconcileFoldSimps au 
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

