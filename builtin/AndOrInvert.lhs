\section{Propositional Theorems (Mixed Operators I)}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AndOrInvert (
  aoiName
, aoiTheory
) where

import Data.Maybe

import Symbols

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
import Conjunction
import TestRendering
\end{code}

\subsection{Introduction}

We supply conjectures here for each theorem in \cite{gries.93}
in the second part of the \textsc{Conjunction} section,
which deals with laws involving a mix of conjunctions and other
previously defined operators.


Some useful local definitions:
\begin{code}
p = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "R") PredV Static
s = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "S") PredV Static
\end{code}

\subsubsection{Known Variables}

We have none.
\begin{code}
aoiKnown :: VarTable
aoiKnown =  newNamedVarTable aoiName
\end{code}

\subsection{MixOne Conjectures}


$$
\CONJPROPMIXONE
$$


$$
  \begin{array}{ll}
     \CJAndOrAbs & \CJAndOrAbsN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjAndOrAbs
 = ( "and" -.- "or" -.- "absorb"
   , ( p /\ ( p \/ q) === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJOrAndAbs & \CJOrAndAbsN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrAndAbs
 = ( "or" -.- "and" -.- "absorb"
   , ( p \/ ( p /\ q) === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJAndOrNAbs & \CJAndOrNAbsN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjAndOrNAbs
 = ( "and" -.- "not" -.- "or" -.- "absorb"
   , ( p /\ ( mkNot p \/ q) === p /\ q
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJOrAndNAbs & \CJOrAndNAbsN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrAndNAbs
 = ( "and" -.- "not" -.- "or" -.- "absorb"
   , ( p \/ ( mkNot p /\ q) === p \/ q
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJOrAndDistr & \CJOrAndDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrAndDistr
 = ( "or" -.- "and" -.- "distr"
   , ( p \/ ( q /\ r) === (p \/ q) /\ (p \/ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJAndOrDistr & \CJAndOrDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjAndOrDistr
 = ( "and" -.- "or" -.- "distr"
   , ( p /\ ( q \/ r) === p /\ q \/ p /\ r
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJdeMorganNand & \CJdeMorganNandN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjDeMorganNand
 = ( "deMorgan" -.- "and"
   , ( mkNot (p /\ q) === mkNot p \/ mkNot q
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJdeMorganNor & \CJdeMorganNorN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjDeMorganNor
 = ( "deMorgan" -.- "or"
   , ( mkNot (p \/ q) === mkNot p /\ mkNot q
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJEqvRepl & \CJEqvReplN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjEqvRepl
 = ( "eqv" -.- "replace"
   , ( (p===q) /\ (r===p) === (p===q) /\ (r===q)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
    \CJEqvDef & \CJEqvDefN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjEqvDef
 = ( "eqv" -.- "def"
   , ( flattenEquiv ( (p===q) === (p /\ q) \/ (mkNot p /\ mkNot q) )
     , scTrue ) )
\end{code}



Assemble it all:
\begin{code}
aoiConjs :: [NmdAssertion]
aoiConjs = map mkNmdAsn
    [ cjOrAndAbs, cjAndOrNAbs, cjOrAndNAbs
    , cjOrAndDistr, cjAndOrDistr
    , cjDeMorganNand, cjDeMorganNor
    , cjEqvRepl
    , cjEqvDef
    ]
\end{code}

\subsection{The And-Or-Invert Theory}

\begin{code}
aoiName :: String
aoiName = "AOI"
aoiTheory :: Theory
aoiTheory
  =  nullTheory { thName  =  aoiName
            , thDeps  =  [ conjName, disjName, notName, equivName ]
            , known   =  aoiKnown
            , conjs   =  aoiConjs
            }
\end{code}
