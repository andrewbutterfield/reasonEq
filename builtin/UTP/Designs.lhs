\chapter{UTP Designs}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.Designs (
  tok, tok' 
, i_design, design
, designName
, designTheory
) where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Substitution
import Theories

import StdTypeSignature
import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import Implication
import Equality
import ForAll
import Exists
import UClose
import StdTypeSignature
import UTP.Reading
import UTP.While.RefineSig
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we define the UTP concept of Designs,
along with the relevant observables, 
constructors,
healthiness conditions,
and related theorems.

\section{Observables}

We have two Design-specific observables\cite[Defn 3.0.1, p75]{UTP-book}:
$$ 
  ok, ok' : \Bool
$$

\begin{code}
ok = jId "ok"  ;  vok = PreVar ok ; vok' = PostVar ok
tok = jVar bool vok  ;  tok' = jVar bool vok'
\end{code}




\section{The Design Theory}


\subsection{Known Variables}

\begin{code}
designKnown :: VarTable
designKnown =  fromJust $ addKnownVar v_design boolf_2 
                        $ newNamedVarTable designName
\end{code}


\subsection{Design Axioms}

Given a pre-condition $P$ and post-condition $Q$ 
over an alphabet that does not mention $ok$ or $ok'$,
we define a constructor that produces a health predicate that does include them:
$$ P \design Q $$
\begin{code}
vP = Vbl (jId "P") PredV Static ; p = fromJust $ pVar ArbType vP ; gP = StdVar vP
vQ = Vbl (jId "Q") PredV Static ; q = fromJust $ pVar ArbType vQ ; gQ = StdVar vQ
design :: Term -> Term -> Term
i_design    =  jId "design"
v_design    =  Vbl i_design ObsV Static
design p q  =  Cons arbpred False i_design [p, q]
\end{code}

From: \cite[Defn 3.1.1, p76]{UTP-book}:
$$
  \begin{array}{lll}
     P \design Q ~\defs~ ok \land P \implies ok' \land Q &
     & \QNAME{$\design$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
designIntro = mkConsIntro i_design boolf_2
(axDsgDef,alDsgDef) = bookdef ("refines" -.- "def") "defd1.5p34"
                         (design p q === (tok /\ p ==> tok' /\ q))
                         scTrue
\end{code}



\begin{code}
designAxioms :: [Law]
designAxioms  =  map labelAsAxiom [ axDsgDef ]
\end{code}

\subsection{Design Conjectures}


Pulling them all together:
\begin{code}
designConjs :: [NmdAssertion]
designConjs
  = [ 
    ]
\end{code}


\begin{code}
designName :: String
designName = "Designs"
designTheory :: Theory
designTheory
  =  nullTheory { thName  =  designName
                , thDeps  =  [ aoiName
                            , conjName
                            , disjName
                            , notName
                            , equivName ]
                , known   =  designKnown
                , laws    =  designAxioms
                , conjs   =  designConjs
                }
\end{code}


