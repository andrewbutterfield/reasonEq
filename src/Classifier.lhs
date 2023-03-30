\section{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier where

import qualified Data.Set as S
import Laws
import AST
import Assertions
import LexBase

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

combineAuto :: AutoLaws -> AutoLaws -> AutoLaws
combineAuto a b = AutoLaws {  simps = simps a ++ simps b
                            , folds = folds a ++ folds b
                            , unfolds = unfolds a ++ unfolds b
                            }

showDir :: Direction -> String
showDir Leftwards  = "Leftwards"
showDir Rightwards = "Rightwards"

simpStr :: (String, Direction) -> String
simpStr sim = "(" ++ fst sim ++ "," ++ showDir (snd sim) ++ ")"

showSimps :: [(String, Direction)] -> Int -> String
showSimps [] _ = ""
showSimps (x:[]) n = "\n\t" ++ show n ++ ". " ++ simpStr x
showSimps (x:xs) n = "\n\t" ++ show n ++ ". " ++ simpStr x ++ showSimps xs (n + 1)

showFolds :: [String] -> Int -> String
showFolds [] _ = ""
showFolds (x:[]) n = "\n\t" ++ show n ++ ". " ++ x
showFolds (x:xs) n = "\n\t" ++ show n ++ ". " ++ x ++ showFolds xs (n + 1)

showAuto alaws = "   i. simps:"  ++ showSimps (simps alaws) 1  ++ "\n\n"
              ++ "  ii. folds:"  ++ showFolds (folds alaws) 1  ++ "\n\n"
              ++ " iii. unfolds:"  ++ showFolds (unfolds alaws) 1 ++ "\n\n"

addLawClassifier :: NmdAssertion -> AutoLaws -> AutoLaws
addLawClassifier (nme, asser) au = removeFoldSimps $ AutoLaws {  simps = simps au ++ addSimp nme (assnT asser)
                                                                , folds = folds au ++ addFold nme (assnT asser)
                                                                , unfolds = unfolds au ++ addFold nme (assnT asser)
                                                               }

removeFoldSimps :: AutoLaws -> AutoLaws
removeFoldSimps au = AutoLaws {  simps = removeSimpsList (folds au) (simps au)
                               , folds = folds au
                               , unfolds = unfolds au
                              }

removeSimpsList :: [String] -> [(String, Direction)] -> [(String, Direction)]
removeSimpsList [] ys = ys
removeSimpsList (x:xs) ys = removeSimpsList xs $ removeSimp x ys

removeSimp :: String -> [(String, Direction)] -> [(String, Direction)]
removeSimp _ [] = []
removeSimp x (y:ys) | x == fst y    = removeSimp x ys
                    | otherwise = y : removeSimp x ys
                                            
addLawsClass :: [Law] -> AutoLaws -> AutoLaws
addLawsClass [] au = au 
addLawsClass (x:[]) au = (addLawClassifier (lawNamedAssn x) au)
addLawsClass (x:xs) au = addLawsClass (xs) (addLawClassifier (lawNamedAssn x) au)

termSize :: Term -> Int
termSize (Val _ _)            =  1
termSize (Var _ _)            =  1
termSize (Cons _ _ _ ts)      =  1 + sum (map termSize ts)
termSize (Bnd _ _ vs t)       =  1 + S.size vs + termSize t
termSize (Lam _ _ vl t)       =  1 + length vl + termSize t
termSize (Cls _ t)            =  1 + termSize t
termSize (Sub _ t subs)       =  1 + termSize t + subsSize subs
termSize (Iter _ _ _ _ _ vl)  =  3 + length vl
termSize (Typ _)              =  2

subsSize (Substn ts lvs)      =  3 * S.size ts + 2 * S.size lvs

addSimp :: String -> Term -> [(String, Direction)]
addSimp nme (PCons sb (Identifier "equiv" 0) (p:q:[])) = do let sizeP = termSize p
                                                            let sizeQ = termSize q
                                                            if sizeP > sizeQ
                                                              then [(nme, Leftwards)] 
                                                            else if sizeP < sizeQ
                                                              then [(nme, Rightwards)]
                                                            else []
addSimp nme _ = []

addFold :: String -> Term -> [(String)]
addFold nme (PCons sb (Identifier "equiv" 0) (p:q:[])) =  if isFold p
                                                              then if checkQ q (getN p)
                                                                      then [nme] 
                                                                   else []
                                                          else []
addFold nme _ = []

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
checkQ (Cons _ _ n xs@(_:_)) i
            | all isVar xs && n == i = False
            | otherwise = True
checkQ _ _ = True
\end{code}