\chapter{Theory of Sets}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Sets (
  mtset, senum, ssingle, mbr
, subseteq, sunion, sintsct, sdiff, scard
, setAxioms, setName, setTheory
) where

import Data.Maybe
import qualified Data.Map as M

import LexBase
import Variables
import Types
import AST
import SideCond
import VarData
import Substitution
import Laws
import Proofs
import Theories
import StdTypeSignature
import StdSignature
import Equivalence
import Implication
import Equality
import ForAll
import TestRendering

import Arithmetic
\end{code}

\section{Introduction}

Here we present a hard-coded implementation
a very simple theory of (typed) sets.

\section{Sets Signature}


We need to build some infrastructure here.
This consists of the set variables $S$, $S_n$,
type constructor $\Set{}$, and
the constants $\emptyset$, $\mof$, ${\_}$, $\cup$, $\cap$, $\setminus$.


\subsection{Set Types}

These include:
\begin{code}
elemt = TypeVar $ jId "t"
sett  = power elemt
mbr_t t = FunType t (FunType (power t) bool)
setf_1 t = FunType (power t) (power t)
setf_2 t = FunType (power t) (setf_1 t)
subs_t t = FunType (power t) $ FunType (power t) bool
card_t t = FunType (power t) int
\end{code}

\subsection{Set Values/Operators}

\begin{eqnarray*}
   \emptyset &:& \Set t
\\ \setof x &:& \Set t, \qquad  x : t
\\ \mof &:& t \fun \Set t \fun \Bool
\\ \cup,\cap,\setminus &:& \Set t \fun \Set t \fun \Set t
\\ \subseteq &:& \Set t \fun \Set t \fun \Bool
\\ \# && \Set t \fun \Int
\end{eqnarray*}
All of the above are substitutable.
\begin{code}
i_mt = jId "emptyset" ; mtIntro      = mkConsIntro i_mt  sett
i_set = jId "set"   
i_mbr = jId "mbr"     ; inIntro      = mkConsIntro i_mbr $ mbr_t  elemt
i_U = jId "union"     ; unionIntro   = mkConsIntro i_U   $ setf_2 elemt
i_I = jId "intsct"    ; intsctIntro  = mkConsIntro i_I   $ setf_2 elemt
i_D = jId "\\"        ; setdiffIntro = mkConsIntro i_D   $ setf_2 elemt
i_SS = jId "subseteq" ; subsetIntro  = mkConsIntro i_SS  $ subs_t elemt
i_crd = jId "#"       ; cardIntro    = mkConsIntro i_crd $ card_t elemt
\end{code}

\begin{code}
r2T = reconcile2Types ; rTs = reconcileTypes
tOf = termtype ; j2T = join2Types ; jTs = joinTypes  -- shorthand

mtset :: Term
mtset           =  fromJust $ var sett $ StaticVar i_mt
senum :: [Term] -> Term
senum ts        =  Cons (power $ jTs ts) True i_set ts
ssingle :: Term -> Term
ssingle t       =  senum [t]
mbr :: Term -> Term -> Term
mbr e s         =  Cons bool True i_mbr [e,s]
subseteq s1 s2  =  Cons bool          True i_SS  [s1,s2]
sunion s1 s2    =  Cons (j2T s1 s2)   True i_U   [s1,s2]
sintsct s1 s2   =  Cons (j2T s1 s2)   True i_I   [s1,s2]
sdiff s1 s2     =  Cons (j2T s1 s2)   True i_D   [s1,s2]
scard s         =  Cons int           True i_crd [s]
\end{code}


\subsection{Set Constants and Variables}

\begin{code}
vS = ExprVar (jId "S") Static
s = fromJust $ eVar sett vS
vSn n = ExprVar (jId ("S"++show n)) Static
sn n = fromJust $ eVar sett $ vSn n
s1 = sn 1; s2 = sn 2; s3 = sn 3
vx = StaticVar (jId "x"); gvx = StdVar vx
x = fromJust $ eVar elemt vx
vy = StaticVar (jId "y"); gvy = StdVar vy
y = fromJust $ eVar elemt vy
\end{code}

\section{Set Known Variables}

\begin{code}
setKnown :: VarTable
setKnown 
  = mtIntro $
    inIntro $  
    unionIntro $
    intsctIntro $
    setdiffIntro $
    subsetIntro $
    cardIntro $
    newNamedVarTable setName
\end{code}



\section{Set Laws}

We do set-membership first, then set relations equality and subset,
and then work through the three main set operators: 
union, intersection, and difference,
finishing off with set cardinality.

\subsection{Set Membership}

The rest of the axioms are associated with set-operators.
\begin{eqnarray*}
   x \mof \emptyset  &=& \false
\\ x \mof \setof y   &=& x = y
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axMofEmpty = ( "mbr" -.- "emptyset"
             , ( (x `mbr` mtset) `isEqualTo` falseP
             , scTrue ) )
axMofSingle = ( "mbr" -.- "singleton"
             , ( (x `mbr` ssingle y) `isEqualTo` (x `isEqualTo` y)
             , scTrue ) )
cjMofSingle = ( "mbr" -.- "set" -.- "self"
             , ( (x `mbr` ssingle x) `isEqualTo` trueP
             , scTrue ) )
\end{code}

\subsection{Set Relations}

\begin{eqnarray*}
   (S = T) &=&  \forall x \bullet x \mof S \equiv x \mof T
\\ S \subseteq T &=& \forall x \bullet x \mof S \implies x \mof T
\end{eqnarray*}
\begin{code}
axSetEqDef = ( "set" -.- "=" -.- "def"
             , ( (s1 `isEqualTo` s2) 
                 ===
                 forAll [gvx]
                 (x `mbr` s1 === x `mbr` s2)
             , scTrue ) )
axSubSetEqDef = ( "subseteq" -.- "def"
                , ( (s1 `subseteq` s2) 
                    ===
                    forAll [gvx]
                    (x `mbr` s1 ==> x `mbr` s2)
                , scTrue ) )
\end{code}

\subsection{Set Union}

\begin{eqnarray*}
   x \mof (S \cup T)      &=& x \mof S \lor x \mof T
\\ S \cup \emptyset        &=& S
\\ S_1 \cup S_2            &=& S_2 \cup S_1
\\ S_1 \cup (S_2 \cup S_3) &=& (S_1 \cup S_2) \cup S_3
\end{eqnarray*}
\begin{code}
axMofUnion = ( "mbr" -.- "union" -.- "def"
             , ( (x `mbr` (s1 `sunion` s2))
                 ===
                 ((x `mbr` s1) \/ (x `mbr` s2))
             , scTrue ) )
cjURUnit = ( "union" -.- "r" -.- "unit"
           , ( (s `sunion` mtset) `isEqualTo` s
           , scTrue ) )
cjUSymm  = ( "union" -.- "symm"
           , ( (s1 `sunion` s2) `isEqualTo` (s2 `sunion` s1)
           , scTrue ) )
cjUAssoc  = ( "union" -.- "assoc"
           , ( (s1 `sunion` (s2 `sunion` s3)) 
               `isEqualTo` 
               ((s1 `sunion` s2) `sunion` s3)
           , scTrue ) )
\end{code}

\subsection{Set Intersection}

\begin{eqnarray*}
   x \mof (S \cap T) &=& x \mof S \land x \mof T
\\ S \cap \emptyset      &=& \emptyset
\\ S_1 \cap S_2            &=& S_2 \cap S_1
\\ S_1 \cap (S_2 \cap S_3) &=& (S_1 \cap S_2) \cap S_3
\end{eqnarray*}
\begin{code}
axMofIntsct = ( "mbr" -.- "intsct" -.- "def"
             , ( (x `mbr` (s1 `sintsct` s2))
                 ===
                 ((x `mbr` s1) /\ (x `mbr` s2))
             , scTrue ) )
cjIZero = ( "intsct" -.- "zero"
           , ( (s `sintsct` mtset) `isEqualTo` mtset 
           , scTrue ) )
cjISymm  = ( "intsct" -.- "symm"
           , ( (s1 `sintsct` s2) `isEqualTo` (s2 `sintsct` s1)
           , scTrue ) )
cjIAssoc  = ( "intsct" -.- "assoc"
           , ( (s1 `sintsct` (s2 `sintsct` s3)) 
               `isEqualTo` 
               ((s1 `sintsct` s2) `sintsct` s3)
           , scTrue ) )
\end{code}

\subsection{Set Difference}

\begin{eqnarray*}
   x \mof (S \setminus T) &=& x \mof S \land \lnot(x \mof T)
\\ S \setminus \emptyset      &=& S
\\ (S_1 \setminus S_2) \setminus S_3 &=& S_1 \setminus (S_2 \cup S_3)
\\ S_1 \setminus (S_2 \setminus S_3) 
   &=& 
   (S_1 \setminus S_2) \cup (S_1 \cap S_3)
\end{eqnarray*}
\begin{code}
axMofDiff = ( "mbr" -.- "\\" -.- "def"
             , ( (x `mbr` (s1 `sdiff` s2))
                 ===
                 ((x `mbr` s1) /\ mkNot(x `mbr` s2))
             , scTrue ) )
cjDRUnit = ( "\\" -.-"r" -.- "unit"
           , ( (s `sdiff` mtset) `isEqualTo` s
           , scTrue ) )
cjDLSymm  = ( "\\" -.- "l" -.- "assoc"
            , ( ((s1 `sdiff` s2) `sdiff` s3)
               `isEqualTo` 
               (s1 `sdiff` (s2 `sunion` s3))
            , scTrue ) )
cjDRSymm  = ( "\\" -.- "r" -.- "assoc"
            , ( (s1 `sdiff` (s2 `sdiff` s3))
               `isEqualTo` 
               ((s1 `sdiff` s2) `sunion` (s1 `sintsct` s3))
            , scTrue ) )
\end{code}


\newpage
\subsection{Mixed Set Operators}

\begin{eqnarray*}
   (S_1 \cup S_2) \cap S_3 &=& (S_1 \cap S_3) \cup (S_2 \cap S_3)
\\ (S_1 \cap S_2) \cup S_3 &=& (S_1 \cup S_3) \cap (S_2 \cup S_3)
\\ (S_1 \cup S_2) \setminus S_3 &=& (S_1 \setminus S_3) \cup (S_2 \setminus S_3)
\\ (S_1 \cap S_2) \setminus S_3 &=& (S_1 \setminus S_3) \cap (S_2 \setminus S_3)
\\ S_1 \setminus (S_2 \cup S_3) &=& (S_1 \setminus S_2) \cap (S_1 \setminus S_3)
\\ S_1 \setminus (S_2 \cap S_3) &=& (S_1 \setminus S_2) \cup (S_1 \setminus S_3)
\\ (S_1 \setminus S_2) \cup S_3 &=& (S_1 \cup S_3) \setminus (S_2 \setminus S_3)
\\ (S_1 \setminus S_2) \cap S_3 &=& (S_1 \cap S_3) \setminus S_2
\end{eqnarray*}
\begin{code}
cjUIDistr = ( "union" -.-"intsct" -.- "distr"
            , ( ( (s1 `sunion` s2) `sintsct` s3 )
                `isEqualTo` 
                ( (s1 `sintsct` s3) `sunion` (s2 `sintsct` s3))
            , scTrue ) )
cjIUDistr = ( "intsct" -.-"union" -.- "distr"
            , ( ( (s1 `sintsct` s2) `sunion` s3 )
                `isEqualTo` 
                ( (s1 `sunion` s3) `sintsct` (s2 `sunion` s3))
            , scTrue ) )
cjUDDistr = ( "union" -.-"\\" -.- "distr"
            , ( ( (s1 `sunion` s2) `sdiff` s3 )
                `isEqualTo` 
                ( (s1 `sdiff` s3) `sunion` (s2 `sdiff` s3))
            , scTrue ) )
cjIDDistr = ( "intsct" -.-"\\" -.- "distr"
            , ( ( (s1 `sintsct` s2) `sdiff` s3 )
                `isEqualTo` 
                ( (s1 `sdiff` s3) `sintsct` (s2 `sdiff` s3))
            , scTrue ) )
cjDURDistr = ( "\\" -.-"union" -.- "r" -.- "distr"
            , ( (s1 `sdiff` (s2 `sunion` s3 ))
                `isEqualTo` 
                ((s1 `sdiff` s2) `sintsct` (s1 `sdiff` s3))
            , scTrue ) )
cjDIRDistr = ( "\\" -.-"intsct" -.- "r" -.- "distr"
            , ( ( s1 `sdiff` (s2 `sintsct` s3 ))
                `isEqualTo` 
                ( (s1 `sdiff` s2) `sunion` (s1 `sdiff` s3))
            , scTrue ) )
cjDULDistr = ( "\\" -.-"union" -.- "l" -.- "distr"
             , ( ((s1 `sdiff` s2) `sunion` s3)
                `isEqualTo` 
                ( (s1 `sunion` s3) `sdiff` (s2 `sdiff` s3))
            , scTrue ) )
cjDILDistr = ( "\\" -.-"intsct" -.- "l" -.- "distr"
             , ( ((s1 `sdiff` s2) `sintsct` s3)
                `isEqualTo` 
                ((s1 `sintsct` s3) `sdiff` s2)
             , scTrue ) )
\end{code}

\subsection{Set Cardinality}

\begin{eqnarray*}
   \#\emptyset &=& 0
\\ \#\setof x &=& 1
\\ \#(S \cup T) &=& \# S + \# T + \#(S \cap T)
\end{eqnarray*}
\begin{code}
axCardEmpty = ( "#" -.- "emptyset" -.- "def"
              , ( scard mtset `isEqualTo` zero
              , scTrue ) )
axCardSingle = ( "#" -.- "single" -.- "def"
              , ( scard (ssingle x) `isEqualTo` one
              , scTrue ) )
axCardUnion = ( "#" -.- "union" -.- "def"
              , ( ( scard (s1 `sunion` s2) )
                  `isEqualTo` 
                  (scard s1 `add` scard s2 `sub` scard (s1 `sintsct` s2))
              , scTrue ) )
\end{code}


We collect these together:
\begin{code}
setAxioms :: [Law]
setAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ axMofEmpty, axMofSingle
      , axSetEqDef, axSubSetEqDef
      , axMofUnion, axMofIntsct, axMofDiff
      , axCardEmpty, axCardSingle, axCardUnion
      ]
\end{code}

\section{Set Conjectures}

$$\begin{array}{ll}
   \AXequalSubst & \AXequalSubstN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjEqualSubst
 = ( "=" -.- "subst"
   , (s === s 
   , scTrue ) )
\end{code}


Collecting \dots
\begin{code}
setConjectures :: [NmdAssertion]
setConjectures
  = map mkNmdAsn 
     [ cjMofSingle
     , cjURUnit, cjUSymm, cjUAssoc 
     , cjIZero, cjISymm, cjIAssoc
     , cjDRUnit, cjDLSymm, cjDRSymm
     , cjUIDistr, cjIUDistr, cjUDDistr, cjIDDistr
     , cjDURDistr, cjDIRDistr, cjDULDistr, cjDILDistr
     ]
\end{code}

\section{The Set Theory}

\begin{code}
setName :: String
setName = "Sets"
setTheory :: Theory
setTheory
  =  nullTheory { thName  =  setName
                , thDeps  =  [ implName
                             , equivName 
                             , equalityName
                             , forallName
                             , arithmeticName
                             ]
                , known   =  setKnown
                , laws    =  setAxioms
                , conjs   =  setConjectures
                }
\end{code}
