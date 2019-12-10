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

import NiceSymbols

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
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
s = fromJust $ pVar $ Vbl (fromJust $ ident "S") PredV Static
vx = Vbl (fromJust $ ident "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (fromJust $ ident "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsubsection{Known Variables}

We have none.

\subsubsection{Substitutability}

$$
  \begin{array}{ll}
     \CJimpSubst & \CJimpSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
implSubAble = M.fromList [(implies,CS)]
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
 = ( "implies" -.- "def"
   , ( flattenEquiv ( p ==> q === (p \/ q === q) )
   , scTrue ) )
\end{code}

\begin{code}
implAxioms :: [Law]
implAxioms  =  map labelAsAxiom [ axImplDef ]
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
 = propdef ( "implies" -.- "def2"
           , (p ==> q) === (mkNot p \/ q) )
\end{code}


\newpage

$$\begin{array}{ll}
  \CJImpMeet & \CJImpMeetN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpMeet
 = propdef ( "implies" -.- "meet"
           , (p ==> q) === (p /\ q === p) )
\end{code}


$$\begin{array}{ll}
  \CJContraPos & \CJContraPosN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjContra
 = propdef ( "contrapostive"
           , (p ==> q) === (mkNot q ==> mkNot p) )
\end{code}


$$\begin{array}{ll}
  \CJImpEqvDistr & \CJImpEqvDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpEqvDistr
 = propdef ( "implies" -.- "equiv" -.- "distr"
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
 = propdef ( "implies" -.- "refl"
           , p ==> p === trueP )
\end{code}



$$\begin{array}{ll}
  \CJImpRZero & \CJImpRZeroN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpRZero
 = propdef ( "implies" -.- "r-zero"
           , p ==> trueP === trueP )
\end{code}


$$\begin{array}{ll}
  \CJImpLUnit & \CJImpLUnitN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpLUnit
 = propdef ( "implies" -.- "l-unit"
           , trueP ==> p === p )
\end{code}


$$\begin{array}{ll}
  \CJNotDefTwo & \CJNotDefTwoN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjNotDef2
 = propdef ( "lnot" -.- "def2"
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
 = propdef ( "implies" -.- "trans"
           , (p==>q)/\(q==>r) ==> (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJEqvImpTrans & \CJEqvImpTransN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjEqvImpTrans
 = propdef ( "equiv" -.- "implies" -.- "trans"
           , (p===q)/\(q==>r) ==> (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJImpEqvTrans & \CJImpEqvTransN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjImpEqvTrans
 = propdef ( "implies" -.- "equiv" -.- "trans"
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
 = propdef ( "ante" -.- "lor" -.- "distr"
           , p \/ q ==> r === (p==>r) /\ (q==>r) )
\end{code}


$$\begin{array}{ll}
  \CJAnteAndDistr & \CJAnteAndDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAnteAndDistr
 = propdef ( "ante" -.- "land" -.- "distr"
           , p /\ q ==> r === (p==>r) \/ (q==>r) )
\end{code}


$$\begin{array}{ll}
  \CJCnsqAndDistr & \CJCnsqAndDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjCnsqAndDistr
 = propdef ( "cnsq" -.- "land" -.- "distr"
           , p ==> q /\ r === (p==>q) /\ (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJCnsqOrDistr & \CJCnsqOrDistrN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjCnsqOrDistr
 = propdef ( "cnsq" -.- "land" -.- "distr"
           , p ==> q \/ r === (p==>q) \/ (p==>r) )
\end{code}


$$\begin{array}{ll}
  \CJAnteAsImpl & \CJAnteAsImplN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjAnteAsImp
 = propdef ( "ante" -.- "as" -.- "implies"
           , (p==>q)==>r === (mkNot p ==> r) /\ (q ==> r) )
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
            , subable =  implSubAble
            , laws    =  implAxioms
            , conjs   =  implConjs
            }
\end{code}
