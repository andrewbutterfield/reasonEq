\section{Propositional Theorems (Disjunction)}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Disjunction (
  disjName
, disjTheory
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
import TestRendering
\end{code}

\subsection{Introduction}

Here we provide axioms and conjectures for $\lor$,
based on \cite{gries.93}.

Some useful local definitions:
\begin{code}
v_or = Vbl theOr ObsV Static
p = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "R") PredV Static
vx = Vbl (fromJust $ ident "x") ObsV Static  ; lvxs = LVbl vx [] []
ve = Vbl (fromJust $ ident "e") ExprV Static ; lves = LVbl ve [] []
sub p = Sub pred1 p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsubsection{Known Variables}

\begin{code}
orKnown :: VarTable
orKnown =  fromJust $ addKnownVar v_or boolf_2 
                    $ newNamedVarTable disjName
\end{code}



\newpage
\subsection{Disjunction Axioms}

$$
  \begin{array}{ll}
     \AXorSymm & \AXorSymmN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrSymm
 = ( "or" -.- "symm"
   , ( p \/ q === q \/ p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorAssoc & \AXorAssocN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrAssoc
 = ( "or" -.- "assoc"
   , ( (p \/ q) \/ r === p \/ (q \/ r)
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorIdem & \AXorIdemN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrIdem
 = ( "or" -.- "idem"
   , ( p \/ p === p
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXorEqvDistr & \AXorEqvDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrEqvDistr
 = ( "or" -.- "eqv" -.- "distr"
   , ( flattenEquiv ( (p \/ (q === r)) === (p \/ q === p \/ r) )
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXexclMdl & \AXexclMdlN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axExclMidl
 = ( "excl-middle"
   , ( p \/ mkNot p
   , scTrue ) )
\end{code}


Gather them all together.
\begin{code}
disjAxioms :: [Law]
disjAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ axOrSymm, axOrAssoc, axOrIdem, axOrEqvDistr, axExclMidl ]
\end{code}

\subsection{Disjunction Conjectures}

We supply conjectures here for each theorem in \cite{gries.93}
in the \textsc{Disjunction} section.

$$
\CONJPROPDISJ
$$


$$
  \begin{array}{ll}
       \CJorZero  & \CJorZeroN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrZero
 = ( "or"-.-"zero"
   , ( (p \/ trueP) === trueP
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJorUnit & \CJorUnitN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrUnit
 = ( "or"-.-"unit"
   , ( (p \/ falseP) === p
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJorDistr & \CJorDistrN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrOrDistr
 = ( "or"-.-"or"-.-"distr"
   , ( p \/ (q \/ r) === (p \/ q) \/ (p \/ r)
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \CJorEqvSplit & \CJorEqvSplitN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrEqvSplit
 = ( "or"-.-"eqv"-.-"split"
   , ( flattenEquiv ( (p \/ q === p \/ mkNot q) === p )
     , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
       \AXorSubst & \AXorSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjOrSubst
 = ( "or"-.-"subst"
   , ( sub (p \/ q) === sub p \/ sub q
     , scTrue ) )
\end{code}




\begin{code}
disjConjs :: [NmdAssertion]
disjConjs
  = map mkNmdAsn
     [ cjOrZero, cjOrUnit, cjOrOrDistr, cjOrEqvSplit
     , cjOrSubst
     ]
\end{code}

\subsection{The Disjunction Theory}

\begin{code}
disjName :: String
disjName = "Or"
disjTheory :: Theory
disjTheory
  =  nullTheory { thName  =  disjName
            , thDeps  =  [ notName, equivName ]
            , known   =  orKnown
            , laws    =  disjAxioms
            , conjs   =  disjConjs
            }
\end{code}
