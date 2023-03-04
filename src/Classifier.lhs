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

addLawsClassifier :: NmdAssertion -> AutoLaws -> AutoLaws
addLawsClassifier (nme, asser) au = AutoLaws {  simps = simps au ++ addSimp nme (assnT asser)
                                             ,  folds = folds au
                                             ,  unfolds = unfolds au
                                             }

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
\end{code}