\section{Laws}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2021

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Laws
 ( LogicSig(..)
 , flattenTheEquiv, flattenTheImp, flattenTheAnd
 , flattenAssoc
 , LeftRight(..), GroupSpec(..), groupAssoc
 , NmdAssertion
 , Provenance(..)
 , Law, lawName, lawNamedAssn, lawProvenance
 , isAxiom, isProven, isAssumed
 , labelAsAxiom, labelAsProof, labelAsAssumed
 , writeSignature, readSignature
 , showLogic, showKnowns, showNmdAssns, showLaw, showLaws, showConj, showConjs
 , showLeftRight, showGroupSpec
 ) where

import Utilities
import WriteRead
import LexBase
import AST
import SideCond
import Assertions
import NiceSymbols
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for assertions and laws.

\subsection{Logic Signature}

To make the matching work effectively,
we have to identify which constructs play key logical roles,
such as logic values $\true$ and $\false$,
as well as key propositional operators.
A key principle that needs to be followed here is that any identifier
that is used to trigger a partial match
(currently $\equiv$ and $\implies$),
or is added as part of a replacement
(currently $\land$ and $\lor$),
\emph{must} be identified in what we call a \emph{logic signature}.
$$ \true \qquad \false \qquad \equiv \qquad \implies \qquad \land \qquad \lor$$
\begin{code}
data LogicSig
  = LogicSig
     { theTrue  :: Term
     , theFalse :: Term
     , theEqv   :: Identifier
     , theImp   :: Identifier
     , theAnd   :: Identifier
     , theOr    :: Identifier
     }
\end{code}

\newpage
\subsection{Writing and Reading}

\begin{code}
signature = "SIGNATURE"
logicHDR = "BEGIN "++signature ; logicTRL ="END "++signature

trueKEY  = "TRUE = "
falseKEY = "FALSE = "
eqvKEY   = "EQV = "
impKEY   = "IMP = "
andKEY   = "AND = "
orKEY    = "OR = "

writeSignature :: LogicSig -> [String]
writeSignature theSig
  = [ logicHDR
    , trueKEY  ++ show (theTrue theSig)
    , falseKEY ++ show (theFalse theSig)
    , eqvKEY   ++ show (theEqv theSig)
    , impKEY   ++ show (theImp theSig)
    , andKEY   ++ show (theAnd theSig)
    , orKEY    ++ show (theOr theSig)
    , logicTRL ]

readSignature :: MonadFail m => [String] -> m (LogicSig,[String])
readSignature [] = fail "readSignature: no text."
readSignature txts
  = do rest1         <- readThis logicHDR txts
       (true,rest2)  <- readKey  trueKEY readTerm rest1
       (false,rest3) <- readKey  falseKEY readTerm rest2
       (eqv,rest4)   <- readKey  eqvKEY readId rest3
       (imp,rest5)   <- readKey  impKEY readId rest4
       (and,rest6)   <- readKey  andKEY readId rest5
       (or,rest7)    <- readKey  orKEY readId rest6
       rest8         <- readThis logicTRL rest7
       return ( LogicSig{
                  theTrue = true
                , theFalse = false
                , theEqv = eqv
                , theImp = imp
                , theAnd = and
                , theOr  = or }
              , rest8 )
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

\newpage
\subsection{Associative Grouping}

\begin{code}
flattenAssoc :: MonadFail m => Identifier -> Term -> m Term
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
groupAssoc :: MonadFail m => Identifier -> GroupSpec -> Term -> m Term
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
  = unlines' [ "Truth:       " ++ trTerm 0 (theTrue  logicsig)
             , "Falsity:     " ++ trTerm 0 (theFalse logicsig)
             , "Equivalence:   " ++ trId   (theEqv   logicsig)
             , "Implication:   " ++ trId   (theImp   logicsig)
             , "Conjunction:   " ++ trId   (theAnd   logicsig)
             , "Disjunction:   " ++ trId   (theOr    logicsig) ]
\end{code}


Showing known names:
\begin{code}
showKnowns vts = unlines' (map trVarTable vts)
\end{code}

Showing laws:
\begin{code}
showNmdAssns dm nasns  =  numberList (showNmdAssn dm $ nameWidth nasns)  nasns
nameWidth nasns = maximum $ map (nicelength . nicelawname . fst) nasns

showNmdAssn (showT,showSC) w (nm,(trm,sc))
  =    ldq ++ nmh ++ rdq ++ pad w nmh
       ++ "  " ++ showT trm ++ "  "++showSC sc
  where nmh = nicelawname nm

showLaws _ []    =  "NONE."
showLaws dm lws  =  numberList (showLaw dm $ nameWidth $ map fst lws) lws

showLaw dm w ((nm,(trm,sc)),prov)
  =  showProv prov ++ "  " ++ showNmdAssn dm w (nm,(trm,sc))
showProv Axiom           =  _top
showProv (Proven pname)  =  _qed
showProv Assumed         =  "!"

showConjs _ []    =  "NONE."
showConjs dm cjs  =  numberList (showConj dm $ nameWidth $ cjs) cjs

showConj dm w (nm,(trm,sc))
  =  _redQ ++ "  " ++ showNmdAssn dm w (nm,(trm,sc))
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
