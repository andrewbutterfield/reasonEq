\section{Propositional Theorems (Conjunction)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Conjunction (
  conjName
, conjTheory
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
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\land$,
based on \cite{gries.93}.

Some useful local definitions:
\begin{code}
v_and = Vbl theAnd PredV Static
p = fromJust $ pVar 1 $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar 1 $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar 1 $ Vbl (fromJust $ ident "R") PredV Static
vx = Vbl (fromJust $ ident "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (fromJust $ ident "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub pred1 p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsubsection{Known Variables}

\begin{code}
andKnown :: VarTable
andKnown =  fromJust $ addKnownVar v_and boolf_2 $ newVarTable
\end{code}




\newpage
\subsection{Conjunction Axioms}

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

\begin{code}
conjAxioms :: [Law]
conjAxioms  =  map (labelAsAxiom . mkNmdAsn) [ axGoldRule]
\end{code}

\newpage
\subsection{Conjunction Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Conjunction} section.

$$
\CONJPROPCONJ
$$

The absorption rules are in a seperate theory.


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

\newpage
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

$$
  \begin{array}{ll}
     \CJandSubst & \CJandSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjAndSubst
 = ( "land"-.-"subst"
   , ( sub (p /\ q) === sub p /\ sub q
     , scTrue ) )
\end{code}


Pulling it all together:
\begin{code}
conjConjs :: [NmdAssertion]
conjConjs = map mkNmdAsn
    [ cjandSym, cjandAssoc, cjandIdem
    , cjandUnit, cjandZero
    , cjandDistr
    , cjContradict
    , cjAndSubst
    ]
\end{code}

\subsection{The Conjunction Theory}

\begin{code}
conjName :: String
conjName = "And"
conjTheory :: Theory
conjTheory
  =  nullTheory { thName  =  conjName
            , thDeps  =  [ disjName, notName, equivName ]
            , known   =  andKnown
            , laws    =  conjAxioms
            , conjs   =  conjConjs
            }
\end{code}
