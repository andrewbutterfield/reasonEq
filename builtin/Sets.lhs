\chapter{Theory of Sets}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Sets (
  setAxioms, setName, setTheory
) where

import Data.Maybe
import qualified Data.Map as M

import LexBase
import Variables
import AST
import SideCond
import VarData
import Substitution
import Laws
import Proofs
import Theories
import StdTypeSignature
import StdSignature
import Equivalence
import Implication
import TestRendering
\end{code}

\section{Introduction}

Here we present a hard-coded implementation
a very simple theory of sets.
\begin{eqnarray*}
   x \mof \emptyset  &=& \false
\\ x \mof \setof x   &=& \true
\\ x \mof (S \cup T) &=& x \mof S \lor x \mof T
\\ x \mof (S \cap T) &=& x \mof S \land x \mof T
\\ x \mof (S \setminus T) &=& x \mof S \land \lnot(x \mof T)
\\ S \subseteq T &=& \forall x \bullet (x \mof S) \implies (x \mof T)
\\ \#\emptyset &=& 0
\\ \#\setof x &=& 1
\\ \#(S \cup T) &=& \# S + \# T + \#(S \cap T)
\end{eqnarray*}


We need to build some infrastructure here.
This consists of the set variables $S$, $T$ and $g$,
the constants $\mof$, ${\_}$, $\cup$, $\cap$, $\setminus$.

\section{Set Signature}

\subsection{Set Types}

These include:
\begin{code}
elemt = TypeVar $ jId "t"
mbr_t t = FunType t (FunType (power t) bool)
setf_1 t = FunType (power t) (power t)
setf_2 t = FunType (power t) (setf_1 t)
subs_t t = FunType (power t) $ FunType (power t) bool
card_t t = FunType (power t) int
\end{code}

\subsection{Set Operators}

\begin{eqnarray*}
   \mof &:& t \fun \Set t \fun \Bool
\\ \cup,\cap,\setminus &:& \fun \Set t \fun \Set t \fun \Set t
\\ \subseteq &:& \fun \Set t \fun \Set t \fun \Bool
\\ \# && \fun \Set t \fun \Int
\end{eqnarray*}
\begin{code}
i_in = jId "in"     ; inIntro      = mkConsIntro i_in  $ mbr_t  elemt
i_U = jId "union"   ; unionIntro   = mkConsIntro i_U   $ setf_2 elemt
i_I = jId "intsct"  ; intsctIntro  = mkConsIntro i_I   $ setf_2 elemt
i_D = jId "\\"      ; setdiffIntro = mkConsIntro i_D   $ setf_2 elemt
i_SS = jId "subset" ; subsetIntro  = mkConsIntro i_SS  $ subs_t elemt
i_crd = jId "#"     ; cardIntro    = mkConsIntro i_crd $ card_t elemt
\end{code}

\begin{code}
mbr :: Term -> Term -> Term
mbr e s = Cons (mbr_t elemt) True i_in [e,s]
\end{code}



\subsection{Set Constants and Variables}

\begin{code}
vS = Vbl (jId "S") ExprV Static
s = fromJust $ eVar ArbType vS
\end{code}

\section{Set Known Variables}

\begin{code}
eqKnown :: VarTable
eqKnown =  newVarTable
\end{code}



\section{Set Axioms}

$$\begin{array}{ll}
   \AXequalRefl & \AXequalReflN
\end{array}$$

\vspace{-8pt}
\begin{code}
axEqualRefl
 = ( "=" -.- "refl"
   , ( s `isEqualTo` s
   , scTrue ) )
\end{code}



We collect these together:
\begin{code}
setAxioms :: [Law]
setAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [  ]
\end{code}

\section{Set Conjectures}

$$\begin{array}{ll}
   \AXequalSubst & \AXequalSubstN
\end{array}$$

\vspace{-8pt}
\begin{code}
cjEqualSubst
 = ( "=" -.- "subst"
   , (s === s 
   , scTrue ) )
\end{code}


Collecting \dots
\begin{code}
setConjectures :: [NmdAssertion]
setConjectures
  = map mkNmdAsn [  ]
\end{code}

\section{The Set Theory}

\begin{code}
setName :: String
setName = "Sets"
setTheory :: Theory
setTheory
  =  nullTheory { thName  =  setName
                , thDeps  =  [ implName
                             , equivName ]
                , known   =  eqKnown
                , laws    =  setAxioms
                , conjs   =  setConjectures
                }
\end{code}
