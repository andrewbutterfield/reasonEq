\section{Laws}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Laws
 ( LogicSig(..)
 , flattenTheEquiv, flattenTheImp, flattenTheAnd
 , flattenAssoc
 , LeftRight(..), GroupSpec(..), groupAssoc
 , Assertion, NmdAssertion, (-.-)
 , Provenance(..), Law
 , labelAsAxiom, labelAsProof
 , writeSignature, readSignature
 , showLogic, showNmdAssns, showLaw, showLaws, showConj, showConjs
 , showLeftRight, showGroupSpec
 ) where

import Utilities
import WriteRead
import LexBase
import AST
import SideCond
import NiceSymbols
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for assertions and laws.

\subsection{Logic Signature}

To make the matching work effectively,
we have to identify which constructs play the roles
of truth (and falsity!), logical equivalence, implication and conjunctions.
$$ \true \qquad \false \qquad \equiv \qquad \implies \qquad \land $$
\begin{code}
data LogicSig
  = LogicSig
     { theTrue :: Term
     , theFalse :: Term
     , theEqv  :: Identifier
     , theImp  :: Identifier
     , theAnd  :: Identifier
     }
\end{code}

\subsection{Writing and Reading}

\begin{code}
signature = "SIGNATURE"
logicHDR = "BEGIN "++signature ; logicTRL ="END "++signature

trueKEY = "TRUE = "
falseKEY = "FALSE = "
eqvKEY = "EQV = "
impKEY = "IMP = "
andKEY = "AND = "

writeSignature :: LogicSig -> [String]
writeSignature theSig
  = [ logicHDR
    , trueKEY  ++ show (theTrue theSig)
    , falseKEY ++ show (theFalse theSig)
    , eqvKEY   ++ show (theEqv theSig)
    , impKEY   ++ show (theImp theSig)
    , andKEY   ++ show (theAnd theSig)
    , logicTRL ]

readSignature :: Monad m => [String] -> m (LogicSig,[String])
readSignature [] = fail "readSignature: no text."
readSignature txts
  = do rest1         <- readThis logicHDR txts
       (true,rest2)  <- readKey  trueKEY readTerm rest1
       (false,rest3) <- readKey  falseKEY readTerm rest2
       (eqv,rest4)   <- readKey  eqvKEY readId rest3
       (imp,rest5)   <- readKey  impKEY readId rest4
       (and,rest6)   <- readKey  andKEY readId rest5
       rest7         <- readThis logicTRL rest6
       return ( LogicSig{
                  theTrue = true
                , theFalse = false
                , theEqv = eqv
                , theImp = imp
                , theAnd = and }
              , rest7 )
\end{code}

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
assocFlatten i (Cons tk j ts)
      | i == j  = concat $ map (assocFlatten i) ts
assocFlatten _ t = [t]

flattenTheEquiv :: LogicSig -> Term -> Term
flattenTheEquiv theSig t
  = Cons (termkind t) eqv $ assocFlatten eqv t
  where eqv = theEqv theSig

flattenTheAnd :: LogicSig -> Term -> Term
flattenTheAnd theSig t
  = Cons (termkind t) and $ assocFlatten and t
  where and = theAnd theSig
\end{code}

\newpage

For implication, we need a slighty different approach,
as it is only right-associative,
and we have the trading rule involving conjunction.
\begin{code}
flattenTheImp :: LogicSig -> Term -> Term
flattenTheImp theSig t
  | null fas   =  t
  | otherwise  =  Cons tk imp [Cons tk and fas,tc]
  where
    imp = theImp theSig
    (tas,tc) = collectAnte imp t
    and = theAnd theSig
    fas = concat $ map (assocFlatten and) tas
    tk = termkind t

collectAnte imp (Cons tk i [ta,tc])
  | i == imp  = let (tas,tc') = collectAnte imp tc in (ta:tas,tc')
collectAnte imp t = ([],t)
\end{code}

\subsection{Associative Grouping}

\begin{code}
flattenAssoc :: Monad m => Identifier -> Term -> m Term
flattenAssoc assocI t@(Cons tk opI ts)
 | opI == assocI && length ts > 1  =  return $ Cons tk opI $ assocFlatten opI t
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
groupAssoc :: Monad m => Identifier -> GroupSpec -> Term -> m Term
groupAssoc assocI gs (Cons tk opI ts)
 | opI == assocI && length ts > 2  =  groupAssoc' (mkOp tk opI) gs ts
groupAssoc assocI _ _
  =  fail ("groupAssoc: not a '"++trId assocI++"', len > 2")

mkOp tk opI []   =  error "mkOp: no sub-terms"
mkOp tk opI [t]  =  t
mkOp tk opI ts   =  Cons tk opI ts

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

An assertion is simply a predicate term coupled with side-conditions.
\begin{code}
type Assertion = (Term, SideCond)
\end{code}

Conjectures, hypotheses and laws always have names,
so we introduce the idea of a named-assertion:
\begin{code}
type NmdAssertion = (String,Assertion)
\end{code}

A useful utility to generate compound assertion names is:
\begin{code}
n1 -.- n2  =  n1 ++ "_" ++ n2
\end{code}

However, we also want to specify the provenance of each law.
\begin{code}
data Provenance
  = Axiom       -- asserted as True
  | Proven String     -- demonstrated by (named) proof
  deriving (Eq,Show,Read)
\end{code}

A law is a named assertion along with its provenance.
\begin{code}
type Law = (NmdAssertion,Provenance)

labelAsAxiom :: NmdAssertion -> Law
labelAsAxiom  nasn  =  (nasn, Axiom)

labelAsProof :: NmdAssertion -> String -> Law
labelAsProof nasn cnm =  (nasn, Proven cnm)
\end{code}

\subsection{Showing Laws}

\textbf{This should all be done via proper generic rendering code}

Showing signature:
\begin{code}
showLogic logicsig
  = unlines' [ "Truth:       " ++ trTerm 0 (theTrue  logicsig)
             , "Falsity:     " ++ trTerm 0 (theFalse logicsig)
             , "Equivalence:   " ++ trId   (theEqv   logicsig)
             , "Implication:   " ++ trId   (theImp   logicsig)
             , "Conjunction:   " ++ trId   (theAnd   logicsig) ]
\end{code}


Showing laws:
\begin{code}
showNmdAssns nasns  =  numberList (showNmdAssn $ nameWidth nasns)  nasns
nameWidth nasns = maximum $ map (length . fst) nasns

showNmdAssn w (nm,(trm,sc))
  =    ldq ++ nm ++ rdq ++ pad w nm
       ++ "  " ++ trTerm 0 trm ++ "  "++trSideCond sc

showLaws []   =  "Laws: None."
showLaws lws  =  "Laws:\n"
                 ++ numberList (showLaw $ nameWidth $ map fst lws) lws

showLaw w ((nm,(trm,sc)),prov)
  =  showProv prov ++ "  " ++ showNmdAssn w (nm,(trm,sc))
showProv Axiom       =  _top
showProv (Proven pname)  =  _qed

showConjs []   =  "Conjectures: None."
showConjs cjs  =  "Conjectures:\n"
                 ++ numberList (showConj $ nameWidth $ cjs) cjs

showConj w (nm,(trm,sc))
  =  _redQ ++ "  " ++ showNmdAssn w (nm,(trm,sc))
  -- =  "\x2047" ++ "  " ++ showNmdAssn w (nm,(trm,sc))
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
