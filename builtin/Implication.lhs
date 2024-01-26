\section{Propositional Theorems (Implication)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Implication (
  implName
, implTheory
) where

import Data.Maybe
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import AST
import Substitution
import SideCond
import VarData
import Laws
import Proofs
import Theories

import StdTypeSignature
import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\implies$,
based on \cite{gries.93}.

Some useful local definitions:
\begin{code}
v_imp = Vbl theImp PredV Static
p = fromJust $ pVar 1 $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar 1 $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar 1 $ Vbl (fromJust $ ident "R") PredV Static
s = fromJust $ pVar 1 $ Vbl (fromJust $ ident "S") PredV Static
vx = Vbl (fromJust $ ident "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (fromJust $ ident "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub pred1 p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsubsection{Known Variables}

\begin{code}
impKnown :: VarTable
impKnown =  fromJust $ addKnownVar v_imp boolf_2 $ newVarTable
\end{code}


\newpage
\subsection{Implication Axioms}

$$
  \begin{array}{ll}
     \AXimplDef & \AXimplDefN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axImplDef
 = ( "imp" -.- "def"
   , ( p ==> q === (p \/ q === q) 
   , scTrue ) )
\end{code}

\begin{code}
implAxioms :: [Law]
implAxioms  =  map (labelAsAxiom . mkNmdAsn) [ axImplDef ]
\end{code}

\subsection{Implication Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Implication} section.

$$
\CONJPROPIMPL
$$


$$\begin{array}{ll}
  \CJImpDefTwo & \CJImpDefTwoN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpDef2
 = propdef ( "imp" -.- "def2"
           , (p ==> q) === (mkNot p \/ q) )
\end{code}


\newpage

$$\begin{array}{ll}
  \CJImpMeet & \CJImpMeetN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpMeet
 = propdef ( "imp" -.- "meet"
           , (p ==> q) === (p /\ q === p) )
\end{code}


$$\begin{array}{ll}
  \CJContraPos & \CJContraPosN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjContra
 = propdef ( "contrapositive"
           , (p ==> q) === (mkNot q ==> mkNot p) )
\end{code}


$$\begin{array}{ll}
  \CJImpEqvDistr & \CJImpEqvDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpEqvDistr
 = propdef ( "imp" -.- "eqv" -.- "distr"
           , (p ==> (q === r)) === ((p ==> q) === (p ==> r)) )
\end{code}

$$\begin{array}{ll}
  \CJShunting & \CJShuntingN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjShunting
 = propdef ( "shunting"
           , (p /\ q ==> r) === (p ==> (q ==> r)) )
\end{code}


$$\begin{array}{ll}
  \CJAndImp & \CJAndImpN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAndImp
 = propdef ( "GS3.66"
           , p /\ (p ==> q) === p /\ q  )
\end{code}


$$\begin{array}{ll}
  \CJAndPmi & \CJAndPmiN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAndPmi
 = propdef ( "GS3.67"
           , p /\ (q ==> p) === p  )
\end{code}


$$\begin{array}{ll}
  \CJOrImp & \CJOrImpN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjOrImp
 = propdef ( "GS3.68"
           , p \/ (p ==> q) === trueP )
\end{code}



$$\begin{array}{ll}
  \CJOrPmi & \CJOrPmiN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjOrPmi
 = propdef ( "GS3.69"
           , p \/ (q ==> p) === q ==> p )
\end{code}


$$\begin{array}{ll}
  \CJOrImpAnd & \CJOrImpAndN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjOrImpAnd
 = propdef ( "GS3.70"
           , p \/ q ==> p /\ q === (p === q) )
\end{code}

\newpage

$$\begin{array}{ll}
  \CJImpRefl & \CJImpReflN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpRefl
 = propdef ( "imp" -.- "refl"
           , p ==> p === trueP )
\end{code}



$$\begin{array}{ll}
  \CJImpRZero & \CJImpRZeroN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpRZero
 = propdef ( "imp" -.- "r-zero"
           , p ==> trueP === trueP )
\end{code}


$$\begin{array}{ll}
  \CJImpLUnit & \CJImpLUnitN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpLUnit
 = propdef ( "imp" -.- "l-unit"
           , trueP ==> p === p )
\end{code}


$$\begin{array}{ll}
  \CJNotDefTwo & \CJNotDefTwoN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjNotDef2
 = propdef ( "not" -.- "def2"
           , p ==> falseP === mkNot p )
\end{code}


$$\begin{array}{ll}
  \CJFalseImp & \CJFalseImpN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjFalseImp
 = propdef ( "GS3.75"
           , falseP ==> p === trueP )
\end{code}


$$\begin{array}{ll}
  \CJImpTrans & \CJImpTransN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpTrans
 = propdef ( "imp" -.- "trans"
           , (p==>q)/\(q==>r) ==> (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJEqvImpTrans & \CJEqvImpTransN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjEqvImpTrans
 = propdef ( "eqv" -.- "imp" -.- "trans"
           , (p===q)/\(q==>r) ==> (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJImpEqvTrans & \CJImpEqvTransN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpEqvTrans
 = propdef ( "imp" -.- "eqv" -.- "trans"
           , (p==>q)/\(q===r) ==> (p==>r) )
\end{code}

\newpage

$$\begin{array}{ll}
  \CJAnteStrngthn & \CJAnteStrngthnN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAnteStr
 = propdef ( "strengthen" -.- "ante"
           , p /\ q ==> p )
\end{code}


$$\begin{array}{ll}
  \CJCnsqWkn & \CJCnsqWknN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjCnsqWkn
 = propdef ( "weaken" -.- "cnsq"
           , p ==> p \/ q  )
\end{code}


$$\begin{array}{ll}
  \CJAnteOrDistr & \CJAnteOrDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAnteOrDistr
 = propdef ( "ante" -.- "or" -.- "distr"
           , p \/ q ==> r === (p==>r) /\ (q==>r) )
\end{code}


$$\begin{array}{ll}
  \CJAnteAndDistr & \CJAnteAndDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAnteAndDistr
 = propdef ( "ante" -.- "and" -.- "distr"
           , p /\ q ==> r === (p==>r) \/ (q==>r) )
\end{code}


$$\begin{array}{ll}
  \CJCnsqAndDistr & \CJCnsqAndDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjCnsqAndDistr
 = propdef ( "cnsq" -.- "and" -.- "distr"
           , p ==> q /\ r === (p==>q) /\ (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJCnsqOrDistr & \CJCnsqOrDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjCnsqOrDistr
 = propdef ( "cnsq" -.- "and" -.- "distr"
           , p ==> q \/ r === (p==>q) \/ (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJAnteAsImpl & \CJAnteAsImplN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAnteAsImp
 = propdef ( "ante" -.- "as" -.- "imp"
           , (p==>q)==>r === (mkNot p ==> r) /\ (q ==> r) )
\end{code}


$$\begin{array}{ll}
  \CJimpSubst & \CJimpSubstN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpSubst
 = propdef ( "imp" -.- "subst"
           , sub ( p ==> q) === sub p ==> sub q )
\end{code}



Pulling them all together:
\begin{code}
implConjs :: [NmdAssertion]
implConjs
  = [ cjImpDef2
    , cjImpMeet, cjContra, cjImpEqvDistr, cjShunting
    , cjAndImp, cjAndPmi, cjOrImp, cjOrPmi, cjOrImpAnd
    , cjImpRefl, cjImpRZero, cjImpLUnit, cjNotDef2, cjFalseImp
    , cjImpTrans, cjEqvImpTrans, cjImpEqvTrans
    , cjAnteStr, cjCnsqWkn
    , cjAnteOrDistr, cjAnteAndDistr, cjCnsqOrDistr, cjCnsqAndDistr
    , cjAnteAsImp
    , cjImpSubst
    ]
\end{code}

\subsection{The Implication Theory}

\begin{code}
implName :: String
implName = "Implies"
implTheory :: Theory
implTheory
  =  nullTheory { thName  =  implName
            , thDeps  =  [ aoiName
                         , conjName
                         , disjName
                         , notName
                         , equivName ]
            , known   =  impKnown
            , laws    =  implAxioms
            , conjs   =  implConjs
            }
\end{code}
