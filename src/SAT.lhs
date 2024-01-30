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
  , supportedOps
  , satsolve
  ) where
    
import Data.List ( nub, subsequences )
import Data.Maybe ( listToMaybe )
import LexBase
import AST
import TestRendering ( trTerm )

import Debug.Trace
\end{code}

\subsection{Supported Terms}

For now, this SAT solver only works for terms built from values, variables,
negation, and \emph{binary} applications of logical and, or, implies,
and equivalence.
\begin{code}
supportedOps :: Term -> Bool
supportedOps (Val _ _) = True
supportedOps (Var _ _) = True
supportedOps (Cons _ _ (Identifier nm _) xs)
  | (nm == "and") || (nm == "not") || (nm == "or") 
    || (nm == "eqv") || (nm == "imp")
       = all supportedOps xs
  | otherwise = False
supportedOps t = False

unsupportedError :: [Char] -> Term -> a
unsupportedError fnname t 
  = error ("SAT."++fnname++" used on non-supported term: "++trTerm 0 t)
\end{code}

\subsection{Formula Normalisation}

$$ P \equiv Q \mbox{ is }  (P \implies Q) \land (Q \implies P) $$

\begin{code}
equivFree :: Term -> Term
equivFree x@(Val a b) = x
equivFree x@(Var a b) = x
equivFree t@(Cons a b (Identifier nm _) xs)
  | nm == "eqv" = equivFree (equivFreeNested t)
  | otherwise = Cons a b (jId nm) (map equivFree xs)
equivFree t = unsupportedError "equivFree" t

equivFreeNested :: Term -> Term
equivFreeNested (Cons a b (Identifier nm _) [p,q]) 
  = Cons a b (jId "and") 
             [ Cons a b (jId "imp") 
                        [equivFree p, equivFree q]
             , Cons a b (jId "imp") [equivFree q, equivFree p]]
equivFreeNested (Cons a b (Identifier nm _) (p:q:rest)) 
  = equivFreeNested 
     (Cons a b (jId nm) 
       ( Cons a b (jId "and") 
                    [ Cons a b (jId "imp") [p, q]
                    , Cons a b (jId "imp") [q, equivFree p]
                    ]
         : rest ))
equivFreeNested t = unsupportedError "equivFreeNested" t
\end{code}

$$ P \implies Q \mbox{ is }  \lnot P \lor Q $$

\begin{code}
implFree :: Term -> Term
implFree x@(Val a b) = x
implFree x@(Var a b) = x
implFree (Cons a b (Identifier nm _) [p]) = Cons a b (jId nm) [implFree p]
implFree (Cons a b (Identifier nm _) [p,q]) 
  | nm == "imp" 
     = Cons a b (jId "or") 
                [Cons a b (jId "not") [implFree p],implFree q]
  | otherwise = Cons a b (jId nm) [implFree p,implFree q]
implFree t = unsupportedError "implFree" t
\end{code}

Negation normal-form, 
obtained by using DeMorgan's Laws to drive negation down onto variables.

\begin{code}
negateTerm :: Term -> Term
negateTerm t = Cons (termtype t) True (jId "not") [t]
\end{code}


\begin{code}
nnf :: Term -> Term
nnf t@(Val a b) = t
nnf t@(Var a b) = t
nnf (Cons a1 b1 (Identifier nm1 _) [Cons a2 b2 (Identifier nm2 _) [t]])
  | nm1 == "not" && nm2 == "not" =  nnf t
  | otherwise = Cons a1 b1 (jId nm1) [Cons a2 b2 (jId nm2) [nnf t]]
nnf (Cons a b (Identifier nm1 _) [Cons a2 b2 (Identifier nm2 _) [p,q]])  
  | nm1 == "not" && nm2 == "or" 
    = Cons a b (jId "and") [nnf (negateTerm p), nnf (negateTerm q)]       
  | nm1 == "not" && nm2 == "and" 
    = Cons a b (jId "or") [nnf (negateTerm p), nnf (negateTerm q)]    
  | otherwise 
    = Cons a b (jId nm1) [Cons a2 b2 (jId nm2) [nnf p,nnf q]]        
nnf (Cons a b (Identifier nm _) [p,q]) = Cons a b (jId nm) [nnf p, nnf q]
nnf (Cons a b (Identifier nm _) (p:[]))
  | p == Val (termtype p) (Boolean True) = Val (termtype p) (Boolean False)
  | p == Val (termtype p) (Boolean False) = Val (termtype p) (Boolean True)
  | otherwise = Cons a b (jId nm) [nnf p]
nnf t = unsupportedError "nnf" t
\end{code}

Conjunctive normal form:  

\begin{code}
cnf :: Term -> Term
cnf (Cons a b (Identifier nm _) [p,q]) 
  | nm == "and" = Cons a b (jId nm) [cnf p, cnf q]  
  | nm == "or" = distr (cnf p) (cnf q)
cnf t = t

distr :: Term -> Term -> Term
distr (Cons a b (Identifier nm _) [p,q]) t
  | nm == "and" = Cons a b (jId "and") [distr p t, distr q t]
distr t (Cons a b (Identifier nm _) [p,q])
  | nm == "and" = Cons a b (jId "and") [distr p t, distr q t]
distr t1 t2 = Cons (termtype t1) True (jId "or") [t1,t2]
\end{code}

\subsection{DPLL Algorithm}

\begin{code}
getUnitClauses :: Term -> [Term]
getUnitClauses t@(Var _ _) = [t]
getUnitClauses t@(Cons a b (Identifier nm _) [p])
  | nm == "not" = [t]
  | otherwise = []
getUnitClauses t@(Cons a b (Identifier nm _) [p,q])
  | nm == "and" = getUnitClauses p ++ getUnitClauses q
  | otherwise = []
getUnitClauses t = []
\end{code}

\begin{code}
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

applyUnitPropagation :: Term -> [Term] -> Term
applyUnitPropagation  = foldl applyUnassigned
\end{code}

And-Or Simplification

\begin{code}
true  = Val arbpred (Boolean True)
false = Val arbpred (Boolean False)

simplifyFormula :: Term -> Term
simplifyFormula t@(Cons a b (Identifier "and" _) [p,q]) 
  | psimp == true && qsimp == true  =  true
  | psimp == false || qsimp == false = false
  | psimp == true = qsimp
  | qsimp == true = psimp
  | otherwise = Cons a b (jId "and") [psimp, qsimp]
  where
    psimp = simplifyFormula p ; qsimp = simplifyFormula q
simplifyFormula t@(Cons a b (Identifier "or" _) [p,q]) 
  | psimp == true || qsimp == true = true
  | psimp == false = qsimp
  | qsimp == false = psimp
  | otherwise = Cons a b (jId "or") [psimp, qsimp]
  where
    psimp = simplifyFormula p ; qsimp = simplifyFormula q
simplifyFormula t = t
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
cnfSize :: Term -> String
cnfSize t = show $ termSize t
\end{code}

\begin{code}
storeJustification :: String -> [String] -> Term -> (Term, [String])
storeJustification s sx t = (t, sx ++ [s])
\end{code}

Sometimes we expect a boolean value:
\begin{code}
getBool :: Term -> Bool
getBool (Val _ (Boolean b)) = b
getBool t = unsupportedError "getBool" t
\end{code}


\begin{code}
dpllAlg :: Term -> Bool
dpllAlg form
  = let f = simplifyFormula 
              (applyUnitPropagation form (nub $ getUnitClauses form))
        arr = nub $ getAllVariables f
    in case listToMaybe arr of
      Nothing -> getBool $ simplifyFormula f -- do we need another simp?
      Just elem -> 
        do let f1 = applyUnassigned f elem
           let f2 = simplifyFormula f1
           case dpllAlg f2 of
             True  -> True
             False -> 
               do  let elem' 
                        = nnf (Cons (termtype elem) True (jId "not") [elem])
                   let f1' = applyUnassigned f elem'
                   let f2' = simplifyFormula f1'
                   dpllAlg f2'
\end{code}

\begin{code}
dpll :: Term -> Bool
dpll t  =  dpllAlg $ simplifyFormula $ cnf $ nnf $ implFree $ equivFree t
\end{code}


Given a predicate $P$ we first check it.
If $P$ is not satisfiable we declare it to be $false$.
If satisfiable, we check $\lnot P$.
If $\lnot P$ is not satisfiable then we declare $P$ to be $true$.
Otherwise, neither $P$ nor $\lnot P$ are satisfiable,
so $P$ is declared to be \emph{contingent}.
\begin{code}
satsolve :: MonadFail m => Term -> m (Bool, Bool)
satsolve goalt
  | supportedOps goalt
    = if dpll goalt
         then if dpll invertedt 
                 then fail "contingent term"
                 else return (True,False)
         else return (False,True)
  | otherwise  =  fail "unsupported term"
  where invertedt = negateTerm goalt
\end{code}
