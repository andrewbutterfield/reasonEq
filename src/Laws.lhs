\section{Laws}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Laws
 ( TheLogic(..), flattenTheEquiv, flattenTheImp, flattenTheAnd
 , Assertion, NmdAssertion, Provenance(..), Law
 , labelAsAxiom
 , showLogic, showNmdAssns, showLaw, showLaws
 ) where

import Utilities
import LexBase
import AST
import SideCond
import NiceSymbols
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for assertions and laws.

\subsection{Logic Signature}

To make the matching work effectively,
we have to identify which constructs play the roles
of truth (and falsity!), logical equivalence, implication and conjunctions.
$$ \true \qquad \false \qquad \equiv \qquad \implies \qquad \land $$
\begin{code}
data TheLogic
  = TheLogic
     { theTrue :: Term
     , theFalse :: Term
     , theEqv  :: Identifier
     , theImp  :: Identifier
     , theAnd  :: Identifier
     }
\end{code}

\subsubsection{Predicate Conditioning}

We also want to provide a way to ``condition'' predicates
to facilitate matching  and proof flexibility.
In particular, we expect the following laws to hold:
\begin{eqnarray*}
   P \equiv (Q \equiv R) &=& (P \equiv (Q \equiv R))
\\ &=& P \equiv Q \equiv R
\\ P \land (Q \land R) &=& (P \land (Q \land R))
\\ &=& P \land Q \land R
\\ P \implies (Q \implies R) &=& P \land Q \implies R
\end{eqnarray*}
In particular, we want to ``associatively flatten'' nested
equivalences, conjunctions and conjunctive hypotheses.
\begin{code}
assocFlatten :: Identifier -> Term -> [Term]
assocFlatten i (Cons tk j ts)
      | i == j  = concat $ map (assocFlatten i) ts
assocFlatten _ t = [t]

flattenTheEquiv :: TheLogic -> Term -> Term
flattenTheEquiv theLogic t
  = Cons (termkind t) eqv $ assocFlatten eqv t
  where eqv = theEqv theLogic

flattenTheAnd :: TheLogic -> Term -> Term
flattenTheAnd theLogic t
  = Cons (termkind t) and $ assocFlatten and t
  where and = theAnd theLogic
\end{code}

For implication, we need a slighty different approach,
as it is only right-associative,
and we have the trading rule involving conjunction.
\begin{code}
flattenTheImp :: TheLogic -> Term -> Term
flattenTheImp theLogic t
  | null fas   =  t
  | otherwise  =  Cons tk imp [Cons tk and fas,tc]
  where
    imp = theImp theLogic
    (tas,tc) = collectAnte imp t
    and = theAnd theLogic
    fas = concat $ map (assocFlatten and) tas
    tk = termkind t

collectAnte imp (Cons tk i [ta,tc])
  | i == imp  = let (tas,tc') = collectAnte imp tc in (ta:tas,tc')
collectAnte imp t = ([],t)
\end{code}

\newpage
\subsection{Laws}

An assertion is simply a predicate term coupled with side-conditions.
\begin{code}
type Assertion = (Term, SideCond)
\end{code}

Conjectures, hypotheses and laws always have names,
so we introduce the idea of a named-assertion:
\begin{code}
type NmdAssertion = (String,Assertion)
\end{code}
However, we also want to specify the provenance of each law.
\begin{code}
data Provenance
  = Axiom       -- asserted as True
  | Proven String     -- demonstrated by (named) proof
  deriving (Eq,Show,Read)
\end{code}

A law is a named assertion along with its provenance.
\begin{code}
type Law = (NmdAssertion,Provenance)

labelAsAxiom :: NmdAssertion -> Law
labelAsAxiom  nasn  =  (nasn, Axiom)
\end{code}

\subsection{Showing Laws}

\textbf{This should all be done via proper generic rendering code}

Showing logic:
\begin{code}
showLogic logic
  = unlines' [ "Truth:       " ++ trTerm 0 (theTrue  logic)
             , "Falsity:     " ++ trTerm 0 (theFalse logic)
             , "Equivalence:   " ++ trId   (theEqv   logic)
             , "Implication:   " ++ trId   (theImp   logic)
             , "Conjunction:   " ++ trId   (theAnd   logic) ]
\end{code}


Showing laws:
\begin{code}
showNmdAssns nasns  =  numberList (showNmdAssn $ nameWidth nasns)  nasns
nameWidth lws = maximum $ map (length . fst) lws

showNmdAssn w (nm,(trm,sc))
  =    ldq ++ nm ++ rdq ++ pad w nm
       ++ "  " ++ trTerm 0 trm ++ "  "++trSideCond sc

showLaws lws  =  numberList (showLaw $ nameWidth $ map fst lws) lws

showLaw w ((nm,(trm,sc)),prov)
  =    ldq ++ nm ++ rdq ++ showProv prov ++ pad w nm
    ++ "  " ++ trTerm 0 trm ++ "  "++trSideCond sc
showProv Axiom       =  _subStr "A"
showProv (Proven pname)  =  _subStr "P"
\end{code}
