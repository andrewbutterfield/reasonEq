\chapter{UTP BaseTheory}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.Base (
  i_refines, refines
, i_ndc, ndc
, i_abort, v_abort, abort
, i_miracle, v_miracle, miracle
, utpBase_Conjs, utpBase_Name, utpBase_Theory
, utpBase_Aliases
) where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import Types
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
import Closure
import StdTypeSignature
import UTP.Reading
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we define the ``base'' concepts of UTP theories,
based on the use of complete lattices of predicated ordered by the
refinement relation.
We define four signature items:
refinement (\m{\sqsupseteq}),
non-deterministic choice (\m{\ndc}),
lattice bottom (abort \m{\bot}),
and
lattice top (miracle \m{\top}).
We also provide the semantics for refinement and non-deterministic choice,
as these are ubiqituous.
However, the semantics for lattice top and bottom depend 
on the specific healthiness conditions for a particular theory.


\section{UTP Base Signatures}

\subsection{Refinement}
$$ P \sqsupseteq Q $$
\begin{code}
refines :: Term -> Term -> Term
i_refines    =  jId "refines"
refines p q  =  Cons arbpred False i_refines [p, q]
refinesIntro = mkConsIntro i_refines boolf_2 True
\end{code}

\subsection{Non-deterministic Choice}
$$ P \sqcap Q $$
\begin{code}
ndc :: Term -> Term -> Term
i_ndc    =  jId "sqcap"
ndc p q  =  Cons arbpred True i_ndc [p, q]
ndcIntro = mkConsIntro i_ndc boolf_2 True
\end{code}

\subsection{Abort}
$$ \bot $$
\begin{code}
abort :: Term
i_abort  =  jId "bot"
v_abort  =  Vbl i_abort PredV Static
abort    =  jVar bool v_abort 
abortIntro = mkPredIntro i_abort bool
\end{code}

\subsection{Miracle}
$$ \top $$
\begin{code}
miracle :: Term
i_miracle  =  jId "top"
v_miracle  =  Vbl i_miracle PredV Static
miracle    =  jVar bool v_miracle
miracleIntro = mkPredIntro i_miracle bool
\end{code}

\section{UTP Base Semantics}


\subsection{UTP Refinement}

\subsubsection{Defn. of Refinement}

From \cite[Sec 1.5,p34]{UTP-book},
with addition of the notation using the $\sqsupseteq$ symbol:
$$
  \begin{array}{lll}
     P \sqsupseteq Q ~\defs~ [P \implies Q] &
     & \QNAME{$\sqsupseteq$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(axRefsDef,alRefsDef) = bookdef ("refines" -.- "def") "defd1.5p34"
                         (refines p q === univ (p ==> q))
                         scTrue
\end{code}

\subsubsection{UTP Refinement Laws}


From \cite[Sec 1.5,p35]{UTP-book}
$$
  \begin{array}{lll}
     (P \lor Q \sqsupseteq R)
     \equiv
     (P \sqsupseteq R) \land (Q \sqsupseteq R)  &
     & \QNAME{$\sqsupseteq$-$\lor$-distr}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjRefsOrDistr,alRefsOrDistr)
  = bookdef ("refines" -.- "lor" -.- "distr") "assrt1.5p35"
            ( (p \/ q) `refines` r
              ===
              (p `refines` r) /\ (q `refines` r))
            scTrue
\end{code}

From \cite[Sec 1.5,pp35-36]{UTP-book}
$$
  \begin{array}{lll}
     (P \sqsupseteq Q) \land (Q \sqsupseteq R) \implies (P \sqsupseteq R)  &
     & \QNAME{$\sqsupseteq$-trans}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(cjRefsTrans,alRefsTrans)
  = bookdef ("refines" -.- "trans") "assrt1.5p36a"
            ( (p `refines` q) /\ (q `refines` r)
              ==>
              (p `refines` r) )
            scTrue
\end{code}

Other ``laws'' regarding refinement in Chapter 1:

$$
 [D \land E \implies S] \land [P \implies D] \land [Q \implies E]
 \implies
 [P \land Q \implies S]
 \qquad\textrm{p36}
$$

$$
 F\textrm{ monotonic} \land [Y \implies X] \implies [F(X)\implies F(Y)]
 \qquad\textrm{p37}
$$

$$
[X \land Q \implies S]
\equiv
[X \implies (\forall \lst x \bullet Q \implies S)]
, \textrm{ given }\lst x \notin X
\qquad\textrm{p39}
$$

$$
  [ ( \exists \lst c \bullet D(\lst c)
      \land L(\lst c,\lst a) )
    \implies S(\lst a)
  ]
  \equiv
  [ D(\lst c)
    \implies
    ( \forall \lst a \bullet L(\lst c,\lst a) \implies S(\lst a) )
  ]
, \textrm{ given }\lst c \not{\!\cap}\; \lst a
  \qquad\textrm{p41}
$$

We may implement these later.



\subsection{UTP Non-deterministic Choice}

\subsubsection{Defn. of N.-D.-Choice}

From \cite[Defn 2.4.1,p51]{UTP-book}

$$
  \begin{array}{lll}
     P \sqcap Q = P \lor Q
     && \QNAME{$\sqcap$-def}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
v_ndc = Vbl i_ndc PredV Static
(axNDCDef,alNDCDef) = bookdef ("sqcap" -.- "def") "Def2.4.1"
                         ( p `ndc` q  ===  p \/ q )
                         scTrue
\end{code}

\subsubsection{UTP N.-D.-Choice Laws}

From \cite[2.4\textbf{L1}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap Q = P \lor Q
     && \QNAME{$\sqcap$-symm}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCSymm,alNDCSymm) = bookdef ("sqcap" -.- "symm") "2.4L1"
                         ( p `ndc` q  ===  q `ndc` p )
                         scTrue
\end{code}

From \cite[2.4\textbf{L2}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap Q = P \lor Q
     && \QNAME{$\sqcap$-symm}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCAssoc,alNDCAssoc) = bookdef ("sqcap" -.- "assoc") "2.4L2"
                         ( p `ndc` (q `ndc` r)  ===  (p `ndc` q) `ndc` r )
                         scTrue
\end{code}

From \cite[2.4\textbf{L3}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap P = P
     && \QNAME{$\sqcap$-idemp}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCIdem,alNDCIdem) = bookdef ("sqcap" -.- "idem") "2.4L3"
                         ( p `ndc` p  ===  p )
                         scTrue
\end{code}

From \cite[2.4\textbf{L4}, p52]{UTP-book}
$$
  \begin{array}{lll}
     P \sqcap (Q \sqcap R) = (P \sqcap Q) \sqcap (P \sqcap R)
     && \QNAME{$\sqcap$-self-distr}
  \end{array}
$$ %\par\vspace{-8pt}
\begin{code}
(cjNDCDistr,alNDCDistr)
   = bookdef ("sqcap" -.- "distr") "2.4L4"
             ( p `ndc` (q `ndc` r)  ===  (p `ndc` q) `ndc` (p `ndc` r) )
             scTrue
\end{code}


\newpage
\section{UTP Base Theory}

We collect our known variables:
\begin{code}
utpBase_Knowns
 = refinesIntro $
   ndcIntro $
   abortIntro $
   miracleIntro $
   newNamedVarTable utpBase_Name
\end{code}


We now collect our axiom set:
\begin{code}
utpBase_Axioms :: [Law]
utpBase_Axioms
  = map labelAsAxiom
      [ axRefsDef
      , axNDCDef
      ]
\end{code}


We now collect our conjecture set:
\begin{code}
utpBase_Conjs :: [NmdAssertion]
utpBase_Conjs
  = [ cjRefsOrDistr, cjRefsTrans
    , cjNDCSymm, cjNDCAssoc, cjNDCIdem, cjNDCDistr
    ]
\end{code}


We now collect our alias set:
\begin{code}
utpBase_Aliases :: [(String,String)]
utpBase_Aliases
  = [ alRefsDef, alRefsOrDistr, alRefsTrans
    , alNDCDef, alNDCSymm, alNDCAssoc, alNDCIdem, alNDCDistr
    ]
\end{code}


\begin{code}
utpBase_Name :: String
utpBase_Name = "UBase"
utpBase_Theory :: Theory
utpBase_Theory
  =  nullTheory { thName  =  utpBase_Name
                , thDeps  = [ closureName
                            , existsName
                            , forallName
                            , equalityName
                            , implName
                            , aoiName
                            , conjName
                            , disjName
                            , notName
                            , equivName
                            ]
            , known   =  utpBase_Knowns
            , laws    =  utpBase_Axioms
            , conjs   =  utpBase_Conjs
            }
\end{code}

\section{UTP Base Infrastructure}

\begin{code}
p = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "P") PredV Static
q = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "Q") PredV Static
r = fromJust $ pVar ArbType $ Vbl (fromJust $ ident "R") PredV Static
\end{code}
