\section{SAT Solver}
\begin{verbatim}
Copyright (c) Aaron Bruce       2023 
              Andrew Buttefield 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SAT 
  ( dpll
  , negateTerm
  , supportedOps
  ) where
    
import Data.List ( nub )
import LexBase
import AST
import TestRendering ( trTerm )

import Debug.Trace
\end{code}

For now, this SAT solver only works for terms build from values, variables,
and applications of logical not, and, or, implies and equivalence.
\begin{code}
supportedOps :: Term -> Bool
supportedOps (Val _ _) = True
supportedOps (Var _ _) = True
supportedOps (Cons _ _ (Identifier nm _) xs)
  | (nm == "land") || (nm == "lnot") || (nm == "lor") 
    || (nm == "equiv") || (nm == "implies")
       = all supportedOps xs
  | otherwise = False
supportedOps t = False
{-supportedOps (Bnd _ _ _ t) = False
supportedOps (Lam _ _ _ t) = False
supportedOps (Cls _ t) = False
supportedOps (Sub _ t _) = False
supportedOps (Iter _ _ _ _ _ _) = False
supportedOps(Typ _) = False -}

unsupportedError fnname t 
  = error ("SAT."++fnname++" used on non-supported term: "++trTerm 0 t)
\end{code}


\begin{code}
implFree :: Term -> Term
implFree x@(Val a b) = x
implFree x@(Var a b) = x
implFree (Cons a b (Identifier nm _) [p]) = Cons a b (jId nm) [implFree p]
implFree (Cons a b (Identifier nm _) [p,q]) 
  | nm == "implies" 
     = Cons a b (jId "lor") 
                [Cons a b (jId "lnot") [implFree p],implFree q]
  | otherwise = Cons a b (jId nm) [implFree p,implFree q]
implFree t = unsupportedError "implFree" t
\end{code}

\begin{code}
equivFree :: Term -> Term
equivFree x@(Val a b) = x
equivFree x@(Var a b) = x
equivFree t@(Cons a b (Identifier nm _) xs)
  | nm == "equiv" = equivFree (equivFreeNested t)
  | otherwise = Cons a b (jId nm) (map equivFree xs)
equivFree t = unsupportedError "equivFree" t

equivFreeNested :: Term -> Term
equivFreeNested (Cons a b (Identifier nm _) [p,q]) 
  = Cons a b (jId "land") 
             [ Cons a b (jId "implies") 
                        [equivFree p, equivFree q]
             , Cons a b (jId "implies") [equivFree q, equivFree p]]
equivFreeNested (Cons a b (Identifier nm _) (p:q:rest)) 
  = equivFreeNested 
     (Cons a b (jId nm) 
       ( Cons a b (jId "land") 
                    [ Cons a b (jId "implies") [p, q]
                    , Cons a b (jId "implies") [q, equivFree p]
                    ]
         : rest ))
equivFreeNested t = unsupportedError "equivFreeNested" t
\end{code}

\begin{code}
nnf :: Term -> Term
nnf t@(Val a b) = t
nnf t@(Var a b) = t
nnf (Cons a1 b1 (Identifier nm1 _) [Cons a2 b2 (Identifier nm2 _) [t]])
  | nm1 == "lnot" && nm2 == "lnot" =  nnf t
  | otherwise = Cons a1 b1 (jId nm1) [Cons a2 b2 (jId nm2) [nnf t]]
nnf (Cons a b (Identifier nm1 _) [Cons a2 b2 (Identifier nm2 _) [p,q]])  
  | nm1 == "lnot" && nm2 == "lor" 
    = Cons a b (jId "land") [nnf (negateTerm p), nnf (negateTerm q)]       
  | nm1 == "lnot" && nm2 == "land" 
    = Cons a b (jId "lor") [nnf (negateTerm p), nnf (negateTerm q)]    
  | otherwise 
    = Cons a b (jId nm1) [Cons a2 b2 (jId nm2) [nnf p,nnf q]]        
nnf (Cons a b (Identifier nm _) [p,q]) = Cons a b (jId nm) [nnf p, nnf q]
nnf (Cons a b (Identifier nm _) (p:[]))
  | p == Val (termkind p) (Boolean True) = Val (termkind p) (Boolean False)
  | p == Val (termkind p) (Boolean False) = Val (termkind p) (Boolean True)
  | otherwise = Cons a b (jId nm) [nnf p]
nnf t = unsupportedError "nnf" t
\end{code}

\begin{code}
negateTerm :: Term -> Term
negateTerm t = Cons (termkind t) True (jId "lnot") [t]
\end{code}

\begin{code}
cnf :: Term -> Term
cnf (Cons a b (Identifier nm _) [p,q]) 
  | nm == "land" = Cons a b (jId nm) [cnf p, cnf q]  
  | nm == "lor" = distr (cnf p) (cnf q)
cnf t = t

distr :: Term -> Term -> Term
distr (Cons a b (Identifier nm _) [p,q]) t
  | nm == "land" = Cons a b (jId "land") [distr p t, distr q t]
distr t (Cons a b (Identifier nm _) [p,q])
  | nm == "land" = Cons a b (jId "land") [distr p t, distr q t]
distr t1 t2 = Cons (termkind t1) True (jId "lor") [t1,t2]
\end{code}

\begin{code}
getUnitClauses :: Term -> [Term]
getUnitClauses t@(Var _ _) = [t]
getUnitClauses t@(Cons a b (Identifier nm _) [p])
  | nm == "lnot" = [t]
  | otherwise = []
getUnitClauses t@(Cons a b (Identifier nm _) [p,q])
  | nm == "land" = getUnitClauses p ++ getUnitClauses q
  | otherwise = []
getUnitClauses t = []
\end{code}

\begin{code}
printArray :: [Term] -> String
printArray [] = ""
printArray (x:xs) = trTerm 0 x ++ ", " ++ printArray xs
\end{code}

\begin{code}
getAllVariables :: Term -> [Term]
getAllVariables t@(Val _ _) = []
getAllVariables t@(Var _ _) = [t]
getAllVariables t@(Cons a b (Identifier nm _) [p]) = [t]
getAllVariables (Cons a b (Identifier nm _) [p,q]) 
  = getAllVariables p ++ getAllVariables q
getAllVariables t = unsupportedError "getAllVariables" t
\end{code}

\begin{code}
chooseUnassigned :: [a] -> Maybe a
chooseUnassigned [] = Nothing
chooseUnassigned (x:_) = Just x

applyUnassigned :: Term -> Term -> Term
applyUnassigned p@(Val _ _) _ = p
applyUnassigned p@(Var _ x) (Var tk k)
  | k == x = Val tk (Boolean True)
  | otherwise = p
applyUnassigned p@(Var tk y) (Cons a b (Identifier nm _) [Var _ x])
  | x == y = Val tk (Boolean False)
  | otherwise = p
applyUnassigned p@(Cons _ _ _ [Var _ x]) (Var tk y)
  | x == y = Val tk (Boolean False)
  | otherwise = p
applyUnassigned p@(Cons _ _ _ [Var _ x]) (Cons _ _ _ [Var tk y]) 
  | x == y = Val tk (Boolean True)
  | otherwise = p                                  
applyUnassigned (Cons a b (Identifier nm _) [p,q]) t 
  = Cons a b (jId nm) [applyUnassigned p t, applyUnassigned q t]
applyUnassigned t _ = unsupportedError "applyUnassigned" t
\end{code}

\begin{code}
simplifyFormula :: Term -> Term
simplifyFormula t@(Cons a b (Identifier "land" _) [p,q]) 
  | (simplifyFormula p == Val P (Boolean True)) 
    && (simplifyFormula q == Val P (Boolean True)) = Val P (Boolean True)
  | (simplifyFormula p == Val P (Boolean False)) 
    || (simplifyFormula q == Val P (Boolean False)) = Val P (Boolean False)
  | simplifyFormula p == Val P (Boolean True) = simplifyFormula q
  | simplifyFormula q == Val P (Boolean True) = simplifyFormula p
  | otherwise = Cons a b (jId "land") [simplifyFormula p, simplifyFormula q]
simplifyFormula t@(Cons a b (Identifier "lor" _) (p:q:[])) 
  | (simplifyFormula p == Val P (Boolean True)) 
    || (simplifyFormula q == Val P (Boolean True)) = Val P (Boolean True)
  | simplifyFormula p == Val P (Boolean False) = simplifyFormula q
  | simplifyFormula q == Val P (Boolean False) = simplifyFormula p
  | otherwise = Cons a b (jId "lor") [simplifyFormula p, simplifyFormula q]
simplifyFormula t = t
\end{code}

\begin{code}
checkResult :: Term -> Bool
checkResult (Val _ x)
  | x == Boolean True   =  True
  | x == Boolean False  =  False 
checkResult t = unsupportedError "checkResult" t

applyUnitPropagation :: Term -> [Term] -> Term
applyUnitPropagation  = foldl applyUnassigned
\end{code}

\begin{code}
dpll :: Term -> [String] -> (Bool, [String])
dpll t just 
  =  do let normalisedFormula 
             = simplifyFormula $ cnf $ nnf $ implFree $ equivFree t
        let (f, justification) 
             = storeJustification 
                 ("CNF: " ++ (trTerm 0 $ normalisedFormula)) 
                 just 
                 normalisedFormula
        let (r, sr) = dpllAlg (f, justification)        
        (r,sr)
\end{code}

\begin{code}
storeJustification :: String -> [String] -> Term -> (Term, [String])
storeJustification s sx t = (t, sx ++ [s])
\end{code}

\begin{code}
dpllAlg :: (Term, [String]) -> (Bool, [String])
dpllAlg (form, justification) 
  = let f = simplifyFormula 
              (applyUnitPropagation form (nub $ getUnitClauses form))
        arr = nub $ getAllVariables f
    in case chooseUnassigned arr of
      Nothing -> 
        do let (res, sxr) 
                 = storeJustification 
                     ("Unit Propagation: " ++ trTerm 0 f) 
                     justification 
                     (simplifyFormula f)
           (checkResult res, sxr)
      Just elem -> 
        do let (f1, sx1) 
                  = storeJustification 
                      ( "Unit Propagation: " ++ trTerm 0 f ++ "\n" 
                         ++ "Assigning " ++ trTerm 0 elem ++ " to TRUE in " 
                         ++ trTerm 0 f) 
                      justification (applyUnassigned f elem)
           let f2 = simplifyFormula f1
           let (_, sx2) 
                 = storeJustification 
                     ("Resulting assignment: " ++ trTerm 0 f2) sx1 f2
           case dpllAlg (f2, sx2) of
             (True, sxr) -> (True, sxr)
             (False, sxr') -> 
               do  let elem' 
                         = nnf (Cons (termkind elem) True (jId "lnot") [elem])
                   let (f1', sx1') 
                          = storeJustification 
                              ( "Assigning " ++ trTerm 0 elem' 
                                ++ " to TRUE in " ++ trTerm 0 f) 
                              sxr' (applyUnassigned f elem')
                   let f2' = simplifyFormula f1'
                   let (_, sx2') 
                         = storeJustification 
                             ("Resulting assignment: " ++ trTerm 0 f2') 
                             sx1' f2'
                   case dpllAlg (f2', sx2') of
                     (True, sxr'') -> (True, sxr')
                     (False, sxr'') -> (False, sxr'')
\end{code}