\section{Propositional Theorems (Negation)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropNot (
  propNotName
, propNotTheory
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
import TestRendering
\end{code}

\subsection{Negation Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Negation, Inequivalence and FALSE} section,
except those about inequivalence.

$$
\CONJPROPNOT
$$

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
\end{code}


$$
  \begin{array}{ll}
       \CJswapNot  & \CJswapNotN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjSwapNot
 = ( "lnot"-.-"equiv"-.-"swap"
   , (  (mkNot p === q) === (p === mkNot q)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJnotInvol & \CJnotInvolN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjNotInvol
 = ( "lnot"-.-"invol"
   , ( mkNot (mkNot p) === p
     , scTrue ) )
\end{code}

\newpage
$$
  \begin{array}{ll}
       \CJnotFalse & \CJnotFalseN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjNotFalse
 = ( "false_neg"
   , ( mkNot falseP === trueP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJnotDef   & \CJnotDefN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjNotDef
 = ( "lnot"-.-"def"
   , ( mkNot p === (p === falseP)
     , scTrue ) )
\end{code}




\begin{code}
propNotConjs :: [NmdAssertion]
propNotConjs
  = [ cjSwapNot, cjNotInvol, cjNotFalse, cjNotDef
    ]
\end{code}

\subsection{The Negation Theory}

\begin{code}
propNotName :: String
propNotName = "PropNot"
propNotTheory :: Theory
propNotTheory
  =  Theory { thName  =  propNotName
            , thDeps  =  [propEquivName,propAxiomName]
            , known   =  newVarTable
            , laws    =  []
            , proofs  =  []
            , conjs   =  propNotConjs
            }
\end{code}
