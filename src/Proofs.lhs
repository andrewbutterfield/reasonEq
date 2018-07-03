\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proofs
 ( HowUsed(..)
 , Justification(..), showJustification
 , isSequentSwitch, justSwitched
 , CalcStep
 , Calculation
 , Proof, displayProof
 , showProofs
 , labelAsProven
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.List
--
import Utilities
import LexBase
import Variables
import AST
import SideCond
import TermZipper
import VarData
import Binding
import Matching
import Instantiate
import Laws
-- import Builder
--
import NiceSymbols
import TestRendering
--
-- import Test.HUnit hiding (Assertion)
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for the key concepts behind a proof,
such as the notion of proof strategies,
and proof calculations.

\newpage
\subsection{Proof Structure}

Consider a pre-existing set of laws $\mathcal L$ (axioms plus proven theorems),
and consider that we have a conjecture $C$ that we want to prove.
The most general proof framework we plan to support is the following:
\begin{description}
  \item[Deduction]
    In general we partition $C$ into three components:
    \begin{description}
      \item[Hypotheses]
        A set $\mathcal H = \setof{H_1,\dots,H_n}$, for $n \geq 0$,
        were all unknown variables in the $H_i$
        are temporarily marked as ``known'' (as themselves),
        for the duration of the proof.
      \item[Consequents]
        A pair of sub-conjectures $C_{left}$ and $C_{right}$.
    \end{description}
    We require these to be chosen such that:
    $$ C \quad =  \bigwedge_{i \in 1\dots n} H_i \implies (C_{left} \equiv C_{right})$$
    Our proof is the based upon the sequent:
    $$ \mathcal L,H_1,\dots,H_n \vdash C_{left} \equiv C_{right}$$
    where we use the laws in both $\mathcal L$ and $\mathcal H$ to transform either or both
    of $C_{left}$ and $C_{right}$ until they are the same.
  \item[Calculation]
    We define two kinds of calculation steps:
    \begin{description}
      \item[standard]
        We use a law from $\mathcal L$ or $\mathcal H$ to transform either sub-conjecture:
        \begin{eqnarray*}
           \mathcal L,\mathcal H &\vdash&  C_x
        \\ &=& \textrm{effect of some assertion $A$
                                      in $\mathcal L\cup \mathcal H$
                                      on $C_x$}
        \\ \mathcal L,\mathcal H &\vdash& C'_x
        \end{eqnarray*}
      \item[deductive]
        We select a hypothesis from in front of the turnstile,
        and use the laws and the rest of the hypotheses to transform it.
        We add the transformed version into the hypotheses,
        retaining its original form as well.
        \begin{eqnarray*}
           \mathcal L,\mathcal H &\vdash& C_x
        \\ &\downarrow& \textrm{select $H_i$}
        \\ \mathcal L,\mathcal H\setminus\setof{H_i}
           &\vdash& H_i
        \\ &=& \textrm{effect of some assertion $A$
                                      in $\mathcal L\cup \mathcal H\setminus\setof{H_i}$
                                      on $H_i$}
        \\ \mathcal L,\mathcal H\setminus\setof{H_i}
           &\vdash& H'_i
        \\ &\downarrow& \textrm{restore calculational sequent}
        \\ \mathcal L,\mathcal H\cup\setof{H_{n+1}} &\vdash& C_x \qquad H_{n+1} = H'_i
        \end{eqnarray*}
        We may do a number of calculational steps on $H_i$ before
        restoring the original standard sequent.
    \end{description}
\end{description}

There are a number of strategies we can apply, depending on the structure
of $C$, of which the following three are most basic
\begin{eqnarray*}
   reduce(C)
   &\defs&
   \mathcal L \vdash C \equiv \true
\\ redboth(C_1 \equiv C_2)
   &\defs&
   \mathcal L \vdash C_1 \equiv C_2
\\ assume(H \implies C)
   &\defs&
   \mathcal L,\splitand(H) \vdash (C \equiv \true)
\end{eqnarray*}
where
\begin{eqnarray*}
\\ \splitand(H_1 \land \dots \land H_n)
   &\defs&
   \setof{H_1,\dots,H_n}
\end{eqnarray*}

In addition, we can envisage a step that transforms the shape of
the deduction.
We may have a conjecture with no top-level implication, but which,
after some standard calculation in a sequent with empty $\mathcal H$,
does end up in such a form.
it would be nice to have the possibility of generating a new sequent form
and carrying on from there.

The requirement that the $H_i$ have all their ``unknown'' variables
converted to ``known'' for the proof
means that the tables describing known variables need to be
linked to specific collections of laws.

\subsection{Proof Calculations}

We start with the simplest proof process of all,
namely a straight calculation from a starting assertion
to a specified final assertion, usually being the axiom \true.
We need to have an AST zipper to allow sub-terms to be singled out
for match and replace,
and some way of recording what happened,
so that proofs (complete or partial) can be saved,
restored, and reviewed.

The actions involved in a proof calculation step are as follows:
\begin{itemize}
  \item Select sub-term.
  \item Match against laws.
  \item Select preferred match and apply its replacement.
  \item Record step (which subterm, which law).
\end{itemize}

We need to distinguish between a `live' proof,
which involves a zipper,
and a proof `record',
that records all the steps of the proof
in enough detail to allow the proof to be replayed.

\begin{code}
type CalcStep
  = ( Justification  -- step justification
    , Term )         -- previous term

data Justification
  = SwLeft     -- switch to left consequent
  | SwRight    -- switch to right consequent
  | SwHyp Int  -- switch to hypothesis i
  | CloneH Int -- clone hypothesis i
  | UseLaw
      HowUsed  -- how law was used in proof step
      String   -- law name
      Binding  -- binding from law variables to goal components
      [Int]    -- zipper descent arguments
  deriving (Eq,Show,Read)

isSequentSwitch :: Justification -> Bool
isSequentSwitch SwLeft     =  True
isSequentSwitch SwRight    =  True
isSequentSwitch (SwHyp _)  =  True
isSequentSwitch _          =  False

justSwitched :: [CalcStep] -> Bool
justSwitched []         =  True -- starting a proof is considered a 'switch'
justSwitched ((j,_):_)  =  isSequentSwitch j

data HowUsed
  = ByMatch          -- replace focus with binding(match)
  | ByInstantiation  -- replace focus=true with binding(law)
  deriving (Eq,Show,Read)
\end{code}

\begin{code}
-- temporary

showJustification :: Justification -> String
showJustification SwLeft
  =  "   [switch left]"
showJustification SwRight
  =  "   [switch right]"
showJustification (SwHyp i)
  =  "   [switch hypothesis "++show i++"]"
showJustification (CloneH i)
  =  "   [clone hypothesis "++show i++"]"
showJustification (UseLaw how lnm bind dpath)
  =  "   = '"++showHow how++" "++lnm++"@" ++ show dpath ++ "'"

showHow :: HowUsed -> String
showHow ByMatch = "match"
showHow ByInstantiation = "instantiate"
\end{code}

We then continue with a proof (record):
\begin{code}
type Proof
  = ( String -- assertion name
    , Assertion
    , String -- Strategy
    , Calculation -- Simple calculational proofs for now
    )

labelAsProven :: NmdAssertion -> Proof -> Law
labelAsProven nasn (prfnm,_,_,_) =  (nasn, Proven prfnm)

type Calculation
  = ( Term -- end (or current) term
    , [ CalcStep ] )  -- calculation steps, in proof order


displayProof :: Proof -> String
displayProof (pnm,(trm,sc),strat,(trm',steps))
 = unlines' ( (pnm ++ " : " ++ trTerm 0 trm ++ " " ++ trSideCond sc)
              : ("by '"++strat++"'")
              : "---"
              : ( map shStep steps )
              ++ [trTerm 0 trm'] )

shStep :: CalcStep -> String
shStep ( SwLeft,  t )  =  unlines' [trTerm 0 t, " [switch left]"]
shStep ( SwRight, t )  =  unlines' [trTerm 0 t, " [switch right]"]
shStep ( SwHyp i, t )
  =  unlines' [trTerm 0 t, " [switch hypothesis "++show i++"]"]
shStep ( (UseLaw how lnm bind dpath), trm )
   = unlines' [ trTermZip $ pathTZ dpath trm
              , " = '" ++ showHow how++" "++lnm++" @" ++ show dpath ++ "'"
              , trBinding bind
              ]
\end{code}

\newpage
\subsection{Showing stuff}

\textbf{This should all be done via proper generic rendering code}



Showing Proofs:
\begin{code}
showProofs []      =  "No Proofs yet."
showProofs proofs  =  unlines' $ map ( ('\n':) . displayProof ) proofs
\end{code}
