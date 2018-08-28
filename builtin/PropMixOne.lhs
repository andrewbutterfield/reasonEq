\section{Propositional Theorems (Mixed Operators I)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropMixOne (
  propMixOneName
, propMixOneTheory
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

import PropAxioms
import PropEquiv
import PropNot
import PropDisj
import PropConj
\end{code}

\subsection{MixOne Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the second part of the \textsc{Conjunction} section,
which deals with laws involving a mix of conjunctions and other
previously defined operators.

$$
\CONJPROPMIXONE
$$

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}


$$
  \begin{array}{ll}
     \CJAndOrAbs & \CJAndOrAbsN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjAndOrAbs
 = ( _land -.- _lor -.- "absorb"
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
 = ( _lor -.- _land -.- "absorb"
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
 = ( _land -.- _lnot -.- _lor -.- "absorb"
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
 = ( _land -.- _lnot -.- _lor -.- "absorb"
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
 = ( _lor -.- _land -.- "distr"
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
 = ( _land -.- _lor -.- "distr"
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
 = ( "deMorgan" -.- _land
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
 = ( "deMorgan" -.- _lor
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
 = ( _equiv -.- "replace"
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
 = ( _equiv -.- "def"
   , ( flattenEquiv ( (p===q) === (p /\ q) \/ (mkNot p /\ mkNot q) )
     , scTrue ) )
\end{code}

\newpage
Assemble it all:
\begin{code}
propMixOneConjs :: [NmdAssertion]
propMixOneConjs
  = [ cjAndOrAbs, cjOrAndAbs, cjAndOrNAbs, cjOrAndNAbs
    , cjOrAndDistr, cjAndOrDistr
    , cjDeMorganNand, cjDeMorganNor
    , cjEqvRepl
    , cjEqvDef
    ]
\end{code}

\subsection{The MixOne Theory}

\begin{code}
propMixOneName :: String
propMixOneName = "PropMixOne"
propMixOneTheory :: Theory
propMixOneTheory
  =  Theory { thName  =  propMixOneName
            , thDeps  =  [ propConjName, propDisjName, propNotName
                         , propEquivName, propAxiomName ]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propMixOneConjs
            }
\end{code}
