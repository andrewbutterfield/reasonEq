\section{Laws}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Laws
 ( theTrue, theFalse, theEqv, theNot, theOr,  theAnd, theImp
 , flattenEquiv, flattenImp, flattenAnd
 , flattenAssoc
 , LeftRight(..), GroupSpec(..), groupAssoc
 , NmdAssertion
 , Provenance(..)
 , Law, lawName, lawNamedAssn, lawProvenance
 , isAxiom, isProven, isAssumed
 , labelAsAxiom, labelAsProof, labelAsAssumed
 , showLogic, showKnowns, showNmdAssns
 , showLaw, showLaws, showConj, showConjs
 , showLeftRight, showGroupSpec
 ) where

import Utilities
import Symbols
import WriteRead
import LexBase
import AST
import SideCond
import Assertions
import TestRendering

import Debugger
\end{code}

We define types for assertions and laws.

\newpage
\subsection{Logic Signature}

To make the matching work effectively,
we have to identify which constructs play key logical roles,
such as logic values $\true$ and $\false$,
as well as the key propositional operators.
These \emph{must} be identified in what we call a \emph{logic signature}.
We give these fixed names, and below we show the symbolic forms we use here.
 
\begin{tabular}[h]{|c|c|l|}
\hline
  Name & Symbolic & What
\\\hline
  - & $\true$ & pred. var. \texttt{True} 
\\\hline
  - & $\false$ & pred. var. \texttt{False} 
\\\hline
  eqv & $\equiv$ & Identifier
\\\hline
  imp & $\implies$ & Identifier
\\\hline
  and & $\land$ & Identifier
\\\hline
  or & $\lor$ & Identifier
\\\hline
  not & $\lnot$   & Identifier
\\\hline
\end{tabular}

\begin{code}
theTrue, theFalse :: Term
theTrue  = Val arbpred $ Boolean True
theFalse = Val arbpred $ Boolean False

theEqv, theNot, theOr, theAnd, theImp :: Identifier
theEqv = jId "eqv"
theNot = jId "not"
theOr  = jId "or"
theAnd = jId "and"
theImp = jId "imp"
\end{code}


\newpage
\subsection{Predicate Conditioning}

We also want to provide a way to ``condition'' predicates
to facilitate matching  and proof flexibility.
In particular, we expect the following laws to hold:
\begin{eqnarray*}
   P \equiv (Q \equiv R) &=& (P \equiv (Q \equiv R))
\\ &=& P \equiv Q \equiv R
\\ P \land (Q \land R) &=& (P \land (Q \land R))
\\ &=& P \land Q \land R
\\ P \implies (Q \implies R) &=& P \land Q \implies R
\end{eqnarray*}
In particular, we want to ``associatively flatten'' nested
equivalences, conjunctions and conjunctive hypotheses.
\begin{code}
assocFlatten :: Identifier -> Term -> [Term]
assocFlatten i (Cons tk _ j ts)
      | i == j  = concat $ map (assocFlatten i) ts
assocFlatten _ t = [t]

flattenEquiv :: Term -> Term
flattenEquiv t 
  = Cons (termtype t) True theEqv $ assocFlatten theEqv t

flattenAnd :: Term -> Term
flattenAnd t 
  = Cons (termtype t) True theAnd $ assocFlatten theAnd t
\end{code}

For implication, we need a slighty different approach,
as it is only right-associative,
and we have the trading rule involving conjunction.
\begin{code}
flattenImp :: Term -> Term
flattenImp t
  | null fas   =  t
  | otherwise  =  Cons tk True theImp [Cons tk True theAnd fas,tc]
  where
    (tas,tc) = collectAnte t
    fas = concat $ map (assocFlatten theAnd) tas
    tk = termtype t

collectAnte (Cons tk _ i [ta,tc])
  | i == theImp  = let (tas,tc') = collectAnte tc in (ta:tas,tc')
collectAnte t = ([],t)
\end{code}

\newpage
\subsection{Associative Grouping}

\begin{code}
flattenAssoc :: (Monad m, MonadFail m) => Identifier -> Term -> m Term
flattenAssoc assocI t@(Cons tk sI opI ts)
 | opI == assocI && length ts > 1
     =  return $ Cons tk sI opI $ assocFlatten opI t
flattenAssoc assocI _
     =  fail ("flattenAssoc: not a '"++trId assocI++"', len > 1")
\end{code}

We also want to specify and perform a number
of different ways to group, or ``un-flatten'',
an equivalence (or indeed any associative operator).
First, some types:
\begin{code}
data LeftRight = Lft | Rght deriving (Eq,Show,Read)

data GroupSpec
  = Assoc LeftRight
  | Gather LeftRight Int
  | Split Int
  deriving (Eq,Show,Read)
\end{code}

Then code to do it:
\begin{code}
groupAssoc :: (Monad m, MonadFail m) => Identifier -> GroupSpec -> Term -> m Term
groupAssoc assocI gs (Cons tk sI opI ts)
 | opI == assocI && length ts > 2  =  groupAssoc' (mkOp tk sI opI) gs ts
groupAssoc assocI _ _
  =  fail ("groupAssoc: not a '"++trId assocI++"', len > 2")

mkOp tk sI opI []   =  error "mkOp: no sub-terms"
mkOp tk sI opI [t]  =  t
mkOp tk sI opI ts   =  Cons tk sI opI ts

groupAssoc' mOp (Assoc Lft)      =  gAssocLeft mOp
groupAssoc' mOp (Assoc Rght)     =  gAssocRight mOp
groupAssoc' mOp (Gather Lft i)   =  gGatherLeft mOp i
groupAssoc' mOp (Gather Rght i)  =  gGatherRight mOp i
groupAssoc' mOp (Split i)        =  gSplit mOp i
\end{code}

Left Associative:
\begin{equation*}
 T_1 \oplus T_2 \oplus T_3 \oplus \dots \oplus T_{n-1} \oplus T_n
 \quad\leadsto\quad
  (\dots((T_1 \oplus T_2) \oplus T_3) \oplus \dots \oplus T_{n-1}) \oplus T_n
\end{equation*}
\begin{code}
gAssocLeft mOp []          =  fail "gAssocLeft: no sub-terms"
gAssocLeft mOp [t]         =  return t
gAssocLeft mOp (t1:t2:ts)  =  gAssocLeft mOp (mOp [t1,t2]:ts)
\end{code}

Right Associative:
\[
 T_1 \oplus T_2 \oplus \dots \oplus T_{n-2} \oplus T_{n-1} \oplus T_n
 \quad\leadsto\quad
 T_1 \oplus (T_2 \oplus \dots \oplus (T_{n-2} \oplus (T_{n-1} \oplus T_n))\dots)
\]
\begin{code}
gAssocRight mOp []             =  fail "gAssocRight: no sub-terms"
gAssocRight mOp [t]            =  return t
gAssocRight mOp (t1:ts@(_:_))  =  do ts' <- gAssocRight mOp ts
                                     return $ mOp [t1,ts']
\end{code}

\newpage
Gather $i$ Left:
\[
 T_1 \oplus \dots \oplus T_{i} \oplus T_{i+1} \oplus \dots T_n
 \quad\leadsto\quad
 (T_1 \oplus \dots \oplus T_{i}) \oplus T_{i+1} \oplus \dots T_n
\]
\begin{code}
gGatherLeft mOp i []           =  fail "gGatherLeft: no sub-terms"
gGatherLeft mOp i ts
  | i < 2                      =  fail "gGatherLeft: size too small"
  | null before || null after  =  fail "gGatherLeft: size too large"
  | otherwise                  =  return $ mOp (mOp before:after)
  where (before,after) = splitAt i ts
\end{code}

Gather $i$ Right:
\[
 T_1 \oplus \dots \oplus T_{n-i} \oplus T_{n-i+1} \oplus \dots T_n
 \quad\leadsto\quad
 T_1 \oplus \dots \oplus T_{n-i} \oplus (T_{n-i+1} \oplus \dots T_n)
\]
\begin{code}
gGatherRight mOp i []          =  fail "gGatherRight: no sub-terms"
gGatherRight mOp i ts
  | i < 2                      =  fail "gGatherRight: size too small"
  | null before || null after  =  fail "gGatherRight: size too large"
  | otherwise                  =  return $ mOp (before++[mOp after])
  where (before,after) = splitAt (length ts-i) ts
\end{code}

Split $i$:
\[
 T_1 \oplus \dots \oplus T_{i} \oplus T_{i+1} \oplus \dots T_n
 \quad\leadsto\quad
 (T_1 \oplus \dots \oplus T_{i}) \oplus (T_{i+1} \oplus \dots T_n)
\]
\begin{code}
gSplit mOp i []  =  fail "gSplit: no sub-terms"
gSplit mOp i ts
  | i < 1                      =  fail "gSplit: size too small"
  | null before || null after  =  fail "gGatherLeft: size too large"
  | otherwise                  =  return $ mOp [mOp before,  mOp after]
  where (before,after) = splitAt i ts
\end{code}

\newpage
\subsection{Laws}


Conjectures, hypotheses and laws always have names,
so we introduce the idea of a named-assertion:
\begin{code}
type NmdAssertion = (String,Assertion)
\end{code}

However, we also want to specify the provenance of each law.
\begin{code}
data Provenance
  = Axiom          --  considered as `self-evidently` True
  | Proven String  --  demonstrated by (named) proof
  | Suspect String --  was Proven but a used law has changed
  | Assumed        --  conjecture asserted w/o proof
  deriving (Eq,Show,Read)
\end{code}

A law is a named assertion along with its provenance.
\begin{code}
type Law = (NmdAssertion,Provenance)

lawNamedAssn :: Law -> NmdAssertion
lawNamedAssn = fst

lawProvenance :: Law -> Provenance
lawProvenance = snd

isAxiom, isProven, isAssumed :: Law ->Bool
isAxiom (_,p)  =  p == Axiom
isProven (_,Proven _)  =  True
isProven _ = False
isAssumed (_,p)  =  p == Assumed

lawName :: Law -> String
lawName ((lnm,_),_) = lnm


labelAsAxiom :: NmdAssertion -> Law
labelAsAxiom  nasn  =  (nasn, Axiom)

labelAsProof :: NmdAssertion -> String -> Law
labelAsProof nasn cnm =  (nasn, Proven cnm)

labelAsAssumed :: NmdAssertion -> Law
labelAsAssumed nasn  =  (nasn, Assumed)
\end{code}

\newpage
\subsection{Showing Laws}

\textbf{This should all be done via proper generic rendering code}

Showing signature:
\begin{code}
showLogic logicsig
  = unlines' [ "Truth:       " ++ trTerm 0 theTrue
             , "Falsity:     " ++ trTerm 0 theFalse 
             , "Equivalence: " ++ trId     theEqv   
             , "Implication: " ++ trId     theImp   
             , "Conjunction: " ++ trId     theAnd   
             , "Disjunction: " ++ trId     theOr    
             , "Negation:    " ++ trId     theNot ]
\end{code}


Showing known names:
\begin{code}
showKnowns vts = unlines' (map trVarTable vts)
\end{code}

Showing laws:
\begin{code}
showNmdAssns dm nasns  =  numberList (showNmdAssn dm $ nameWidth nasns)  nasns
nameWidth nasns = maximum $ map (nicelength . truelawname . fst) nasns

showNmdAssn (showT,showSC) w (nm,(Assertion trm sc))
  =    ldq ++ nmh ++ rdq ++ pad w nmh
       ++ "  " ++ showT trm ++ "  "++showSC sc
  where nmh = truelawname nm

showLaws _ []    =  "NONE."
showLaws dm lws  =  numberList (showLaw dm $ nameWidth $ map fst lws) lws

showLaw dm w (nasn,prov)
  =  showProv prov ++ "  " ++ showNmdAssn dm w nasn
showProv Axiom           =  _top
showProv (Proven pname)  =  _qed
showProv Assumed         =  "!"

showConjs _ []    =  "NONE."
showConjs dm cjs  =  numberList (showConj dm $ nameWidth $ cjs) cjs

showConj dm w nasn
  =  _redQ ++ "  " ++ showNmdAssn dm w nasn
\end{code}

Showing associative grouping specifications:
\begin{code}
showLeftRight :: LeftRight -> String
showLeftRight Lft = "left"
showLeftRight Rght = "right"

showGroupSpec :: GroupSpec -> String
showGroupSpec (Assoc lr)
 = "associate "++showLeftRight lr
showGroupSpec (Gather lr i)
 = "gather "++show i++ " on " ++showLeftRight lr
showGroupSpec (Split i) = "split into first " ++ show i ++ " and rest"
\end{code}
