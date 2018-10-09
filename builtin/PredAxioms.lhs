\section{Predicate Axioms}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PredAxioms (
  forall, exists
, predAxioms, predAxiomName, predAxiomTheory
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
import PropMixOne
import PropImpl
import Equality
\end{code}


\newpage
\subsection{Introduction}

Here we present a hard-coded implementation of
predicate equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
However we adopt here a formulation closer to that of Gries\&Schneider,
as the Tourlakis form has useful laws such as the one-point rules
as derived from his axioms by meta-proofs
\emph{that use non-equational reasoning}.
$$
\AXPREDGS
$$

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
and the constants $\forall$ and $\exists$.

\subsection{Predicate Variables}

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
\end{code}

\subsection{Predicate Constants}

\begin{code}
forall = Vbl (fromJust $ ident _forall) PredV Static
exists = Vbl (fromJust $ ident _exists) PredV Static
\end{code}


\subsection{Predicate Axioms}

\subsubsection{Axioms}

$$
  \begin{array}{ll}
     \AXAllTrue & \AXAllTrueN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvRefl
 = ( _forall -.- "true"
   , ( p === p
   , scTrue ) )
\end{code}

%% TEMPLATE
$$
  \begin{array}{ll}
     law & name
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axXXX
 = ( "law" -.- "name"
   , ( p === p
   , scTrue ) )
\end{code}



We now collect all of the above as our axiom set:
\begin{code}
predAxioms :: [Law]
predAxioms
  = map labelAsAxiom
      [ axEqvRefl ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
predAxiomName :: String
predAxiomName = "PredAxioms"
predAxiomTheory :: Theory
predAxiomTheory
  =  Theory { thName  =  predAxiomName
            , thDeps  =  [ equalityName
                         , propImplName
                         , propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName ]
            , known   =  newVarTable
            , laws    =  predAxioms
            , proofs  =  []
            , conjs   =  []
            }
\end{code}
