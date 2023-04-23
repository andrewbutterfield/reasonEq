{-# LANGUAGE PatternSynonyms #-}

module SAT (dpll
          , negateTerm
          , equivFree
          , implFree
          , nnf
          , cnf
          , getUnitClauses
          , applyUnitPropagation
          , simplifyFormula
          , unsupportedOps) where
    
import System.Environment
import System.IO
import System.FilePath
import System.Directory
import System.Exit
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char

import NiceSymbols hiding (help)

import Utilities
import StratifiedDAG
import Persistence
import Files

import LexBase
import Variables
import AST
import VarData
import Binding
import SideCond
import Assertions
import REqState
import StdSignature(propSignature)
import UTPSignature
import Instantiate
import TestRendering
import TestParsing
import REPL
import Dev

import Debug.Trace

implFree :: Term -> Term
implFree x@(Val a b) = x
implFree x@(Var a b) = x
implFree (Cons a b (Identifier nm _) (p:[])) = Cons a b (jId nm) [(implFree p)]
implFree (Cons a b (Identifier nm _) (p:q:[])) 
                              | nm == "implies" = Cons a b (jId "lor") [Cons a b (jId "lnot") [(implFree p)],(implFree q)]
                              | otherwise = Cons a b (jId nm) [(implFree p),(implFree q)]

equivFree :: Term -> Term
equivFree x@(Val a b) = x
equivFree x@(Var a b) = x
equivFree t@(Cons a b (Identifier nm _) xs)
  | nm == "equiv" = equivFree (equivFreeNested t)
  | otherwise = Cons a b (jId nm) (map equivFree xs)

equivFreeNested :: Term -> Term
equivFreeNested (Cons a b (Identifier nm _) (p:q:[])) 
 = Cons a b (jId "land") [Cons a b (jId "implies") [(equivFree p), (equivFree q)], Cons a b (jId "implies") [(equivFree q), (equivFree p)]]
equivFreeNested (Cons a b (Identifier nm _) (p:q:rest)) 
 = equivFreeNested (Cons a b (jId nm) ([(Cons a b (jId "land") [Cons a b (jId "implies") [p, q], Cons a b (jId "implies") [q, equivFree p]])] ++ rest))
                          
nnf :: Term -> Term
nnf t@(Val a b) = t
nnf t@(Var a b) = t
nnf (Cons a1 b1 (Identifier nm1 _) ((Cons a2 b2 (Identifier nm2 _) (t:[])):[])) 
    | nm1 == "lnot" && nm2 == "lnot" =  nnf t
    | otherwise = Cons a1 b1 (jId nm1) [Cons a2 b2 (jId nm2) [(nnf t)]]
nnf (Cons a b (Identifier nm1 _) ((Cons a2 b2 (Identifier nm2 _) (p:q:[])):[]))  
    | nm1 == "lnot" && nm2 == "lor" = Cons a b (jId "land") [(nnf (negateTerm p)), (nnf (negateTerm q))]       
    | nm1 == "lnot" && nm2 == "land" = Cons a b (jId "lor") [(nnf (negateTerm p)), (nnf (negateTerm q))]    
    | otherwise = Cons a b (jId nm1) [Cons a2 b2 (jId nm2) [(nnf p),(nnf q)]]        
nnf (Cons a b (Identifier nm _) (p:q:[])) = Cons a b (jId nm) [(nnf p), (nnf q)]
nnf (Cons a b (Identifier nm _) (p:[]))
    | p == Val (termkind p) (Boolean True) = Val (termkind p) (Boolean False)
    | p == Val (termkind p) (Boolean False) = Val (termkind p) (Boolean True)
    | otherwise = Cons a b (jId nm) [(nnf p)]


negateTerm :: Term -> Term
negateTerm t = Cons (termkind t) True (jId "lnot") [t]

cnf :: Term -> Term
cnf (Cons a b (Identifier nm _) (p:q:[])) 
                                 | nm == "land" = Cons a b (jId nm) [(cnf p), (cnf q)]  
                                 | nm == "lor" = distr (cnf p) (cnf q)
cnf t = t

distr :: Term -> Term -> Term
distr (Cons a b (Identifier nm _) (p:q:[])) t
                                 | nm == "land" = Cons a b (jId "land") [(distr p t), (distr q t)]
distr t (Cons a b (Identifier nm _) (p:q:[]))
                                 | nm == "land" = Cons a b (jId "land") [(distr p t), (distr q t)]
distr t1 t2 = Cons (termkind t1) True (jId "lor") [t1,t2]

getUnitClauses :: Term -> [Term]
getUnitClauses t@(Var _ _) = [t]
getUnitClauses t@(Cons a b (Identifier nm _) (p:[]))
                                          | nm == "lnot" = [t]
                                          | otherwise = []
getUnitClauses t@(Cons a b (Identifier nm _) (p:q:[]))
                                          | nm == "land" = getUnitClauses p ++ getUnitClauses q
                                          | otherwise = []
getUnitClauses t = []

printArray :: [Term] -> String
printArray [] = ""
printArray (x:xs) = (trTerm 0 x) ++ ", " ++ (printArray xs)

getAllVariables :: Term -> [Term]
getAllVariables t@(Val _ _) = []
getAllVariables t@(Var _ _) = [t]
getAllVariables t@(Cons a b (Identifier nm _) (p:[])) = [t]
getAllVariables (Cons a b (Identifier nm _) (p:q:[])) = (getAllVariables p ++ getAllVariables q)

chooseUnassigned :: [a] -> Maybe a
chooseUnassigned [] = Nothing
chooseUnassigned (x:_) = Just x

applyUnassigned :: Term -> Term -> Term
applyUnassigned p@(Val _ _) _ = p
applyUnassigned p@(Var _ x) (Var tk k) | k == x = Val tk (Boolean True)
                                       | otherwise = p
applyUnassigned p@(Var tk y) (Cons a b (Identifier nm _) ((Var _ x):[]))
                                        | x == y = Val tk (Boolean False)
                                        | otherwise = p
applyUnassigned p@(Cons _ _ _ ((Var _ x):[])) (Var tk y)
                                        | x == y = Val tk (Boolean False)
                                        | otherwise = p
applyUnassigned p@(Cons _ _ _ ((Var _ x):[])) (Cons _ _ _ ((Var tk y):[])) 
                                        | x == y = Val tk (Boolean True)
                                        | otherwise = p                                  
applyUnassigned (Cons a b (Identifier nm _) (p:q:[])) t 
                                        = Cons a b (jId nm) [applyUnassigned p t, applyUnassigned q t]

simplifyFormula :: Term -> Term
simplifyFormula t@(Cons a b (Identifier "land" _) (p:q:[])) 
                          | ((simplifyFormula p) == (Val P (Boolean True))) && ((simplifyFormula q) == (Val P (Boolean True))) = Val P (Boolean True)
                          | ((simplifyFormula p) == (Val P (Boolean False))) || ((simplifyFormula q) == (Val P (Boolean False))) = Val P (Boolean False)
                          | simplifyFormula p == (Val P (Boolean True)) = simplifyFormula q
                          | simplifyFormula q == (Val P (Boolean True)) = simplifyFormula p
                          | otherwise = Cons a b (jId "land") [simplifyFormula p, simplifyFormula q]
simplifyFormula t@(Cons a b (Identifier "lor" _) (p:q:[])) 
                          | ((simplifyFormula p) == (Val P (Boolean True))) || ((simplifyFormula q) == (Val P (Boolean True))) = Val P (Boolean True)
                          | simplifyFormula p == (Val P (Boolean False)) = simplifyFormula q
                          | simplifyFormula q == (Val P (Boolean False)) = simplifyFormula p
                          | otherwise = Cons a b (jId "lor") [simplifyFormula p, simplifyFormula q]
simplifyFormula t = t

checkResult :: Term -> Bool
checkResult (Val _ x)
            | x == (Boolean True) = True
            | x == (Boolean False) = False 

applyUnitPropagation :: Term -> [Term] -> Term
applyUnitPropagation formula variables = foldl (\acc variable -> applyUnassigned acc variable) formula variables

unsupportedOps :: Term -> Bool
unsupportedOps (Val _ _) = True
unsupportedOps (Var _ _) = True
unsupportedOps (Cons _ _ (Identifier nm _) xs)
            | (nm == "land") || (nm == "lnot") || (nm == "lor") || (nm == "equiv") || (nm == "implies")
              = and (map unsupportedOps xs)
            | otherwise = False
unsupportedOps t = False
{-unsupportedOps (Bnd _ _ _ t) = False
unsupportedOps (Lam _ _ _ t) = False
unsupportedOps (Cls _ t) = False
unsupportedOps (Sub _ t _) = False
unsupportedOps (Iter _ _ _ _ _ _) = False
unsupportedOps(Typ _) = False -}


dpll :: Term -> [String] -> (Bool, [String])
dpll t just = do let normalisedFormula = simplifyFormula $ cnf $ nnf $ implFree $ equivFree t
                 let (f, justification) = storeJustification ("CNF: " ++ (trTerm 0 $ normalisedFormula) ++ "\n") just normalisedFormula
                 let (r, sr) = dpllAlg (f, justification)        
                 (r,sr)

storeJustification :: String -> [String] -> Term -> (Term, [String])
storeJustification s sx t = (t, (sx ++ [s]))

dpllAlg :: (Term, [String]) -> (Bool, [String])
dpllAlg (form, justification) = let f  = simplifyFormula (applyUnitPropagation form (nub $ getUnitClauses form))
                                    arr = nub $ getAllVariables f
                          in case chooseUnassigned arr of
                            Nothing -> do let (res, sxr) = storeJustification ("Unit Propagation: " ++ (trTerm 0 f) ++ "\n") justification (simplifyFormula f)
                                          (checkResult res, sxr)
                            Just elem -> do let (f1, sx1) = storeJustification ("Unit Propagation: " ++ (trTerm 0 f) ++ "\n" ++"\n" ++ "Assigning " ++ (trTerm 0 elem) ++ " to TRUE in " ++ (trTerm 0 f) ++ "\n") justification (applyUnassigned f elem)
                                            let f2 = simplifyFormula f1
                                            let (_, sx2) = storeJustification ("Resulting assignment: " ++ (trTerm 0 f2) ++ "\n") sx1 f2
                                            case dpllAlg (f2, sx2) of
                                              (True, sxr) -> (True, sxr)
                                              (False, sxr') -> do  let elem' = nnf (Cons (termkind elem) True (jId "lnot") [elem])
                                                                   let (f1', sx1') = storeJustification ("Assigning " ++ (trTerm 0 elem') ++ " to TRUE in " ++ (trTerm 0 f) ++ "\n") sxr' (applyUnassigned f elem')
                                                                   let f2' = (simplifyFormula f1')
                                                                   let (_, sx2') = storeJustification ("Resulting assignment: " ++ (trTerm 0 f2') ++ "\n") sx1' f2'
                                                                   case dpllAlg (f2', sx2') of
                                                                    (True, sxr'') -> (True, sxr')
                                                                    (False, sxr'') -> (False, sxr'')