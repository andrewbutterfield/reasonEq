\section{Propositional Theorems (Conjunction)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropConj (
  propConjName
, propConjTheory
) where

import Data.Maybe

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Theories

import StdSignature
import Equivalence
import Negation
import Disjunction
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\land$,
based on \cite{gries.93}.

Some useful local definitions:
\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
vx = Vbl (fromJust $ ident "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (fromJust $ ident "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsubsection{Known Variables}

We have none.
\begin{code}
conjunctionKnown :: VarTable
conjunctionKnown =  newVarTable
\end{code}




\subsection{TO BE SHIPPED OUT}

$$
  \begin{array}{ll}
     \AXgoldRule & \AXgoldRuleN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axGoldRule
 = ( "golden-rule"
   , ( (p /\ q) === ((p === q) === p \/ q)
   , scTrue ) )
\end{code}

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
shipAxioms :: [Law]
shipAxioms
  = map labelAsAxiom
      [ axGoldRule
      , axImplDef ]
\end{code}

\textbf{END OF STUFF FOR SHIPPING}

\subsection{Conjunction Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Conjunction} section.

$$
\CONJPROPCONJ
$$

The absorption rules are in a seperate theory.


\newpage

$$
  \begin{array}{ll}
       \CJandSymm  & \CJandSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandSym
 = ( "land"-.-"symm"
   , ( (p /\ q) === (q /\ p)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandAssoc & \CJandAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandAssoc
 = ( "land"-.-"assoc"
   , ( (p /\ q) /\ r === p /\ (q /\ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandIdem & \CJandIdemN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandIdem
 = ( "land"-.-"idem"
   , ( p /\ p === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandUnit & \CJandUnitN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandUnit
 = ( "land"-.-"unit"
   , ( p /\ trueP === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandZero & \CJandZeroN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandZero
 = ( "land"-.-"zero"
   , ( p /\ falseP === falseP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJandDistr & \CJandDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjandDistr
 = ( "land"-.-"land"-.-"distr"
   ,  ( p /\ (q /\ r)  === (p /\ q) /\ (p /\ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \CJcontradict & \CJcontradictN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjContradict
 = ( "contradiction"
   , ( p /\ mkNot p === falseP
     , scTrue ) )
\end{code}

\newpage
Pulling it all together:
\begin{code}
propConjConjs :: [NmdAssertion]
propConjConjs
  = [ cjandSym, cjandAssoc, cjandIdem
    , cjandUnit, cjandZero
    , cjandDistr
    , cjContradict
    ]
\end{code}

\subsection{The Conjunction Theory}

\begin{code}
propConjName :: String
propConjName = "PropConj"
propConjTheory :: Theory
propConjTheory
  =  Theory { thName  =  propConjName
            , thDeps  =  [ disjName, notName
                         , equivName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propConjConjs
            }
\end{code}
