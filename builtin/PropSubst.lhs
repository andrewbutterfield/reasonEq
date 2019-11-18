\section{Propositional Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PropSubst (
  propSubstName
, propSubstTheory
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
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropImpl
import TestRendering
\end{code}


\newpage
\subsection{Introduction}


Here we have axioms that state that substitutions
distribute through certain propositional operators.

$$
\AXPROPSUBST
$$

The rest are provable as conjectures:

$$
\CJPROPSUBST
$$

\subsection{Propositional Variables and substitution}

\begin{code}
p = fromJust $ pVar $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static

vx = Vbl (fromJust $ ident "x") ObsV Static
lvxs = LVbl vx [] []

ve = Vbl (fromJust $ ident "e") ExprV Static
lves = LVbl ve [] []

sub p = Sub P p $ fromJust $ substn [] [(lvxs,lves)]
\end{code}

\subsection{Propositional Substitution Axioms}

$$
  \begin{array}{ll}
     \AXtrueSubst & \AXtrueSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axTrueSubst
 = ( "true" -.- "subst"
   , ( sub trueP  === trueP
   , scTrue ) )
\end{code}

$$
  \begin{array}{ll}
     \AXnotSubst & \AXnotSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axNotSubst
 = ( "lnot" -.- "subst"
   , ( sub (mkNot p)  === mkNot (sub p)
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXeqvSubst & \AXeqvSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axEqvSubst
 = ( "equiv" -.- "subst"
   , ( sub (p === q)  === (sub p === sub q)
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \AXorSubst & \AXorSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
axOrSubst
 = ( "lor" -.- "subst"
   , ( sub (p \/ q)  === (sub p \/ sub q)
   , scTrue ) )
\end{code}



We now collect all of the above as our axiom set:
\begin{code}
propSubstAxioms :: [Law]
propSubstAxioms
  = map labelAsAxiom [ axTrueSubst, axNotSubst, axEqvSubst, axOrSubst ]
\end{code}


\subsubsection{Propositional Substitution Conjectures}

$$
  \begin{array}{ll}
     \CJfalseSubst & \CJfalseSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjFalseSubst
 = ( "false" -.- "subst"
   , ( sub falseP  === falseP
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
 = ( "land" -.- "subst"
   , ( sub (p /\ q)  === (sub p /\ sub q)
   , scTrue ) )
\end{code}


$$
  \begin{array}{ll}
     \CJimpSubst & \CJimpSubstN
  \end{array}
$$

\vspace{-8pt}
\begin{code}
cjImplSubst
 = ( "implies" -.- "subst"
   , ( sub (p ==> q)  === (sub p ==> sub q)
   , scTrue ) )
\end{code}


\begin{code}
propSubstConjs :: [NmdAssertion]
propSubstConjs  =  [ cjFalseSubst, cjAndSubst, cjImplSubst ]
\end{code}


\subsection{The Propositional Theory}

\begin{code}
propSubstName :: String
propSubstName = "PropSubst"
propSubstTheory :: Theory
propSubstTheory
  =  Theory { thName  =  propSubstName
            , thDeps  =  [ propImplName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName
                         ]
            , known   =  newVarTable
            , laws    =  propSubstAxioms
            , proofs  =  []
            , conjs   =  propSubstConjs
            }
\end{code}
