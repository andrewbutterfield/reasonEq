\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proofs
 ( HowUsed(..)
 , SeqFocus(..), Justification(..), showJustification
 , isSequentSwitch, justSwitched
 , CalcStep
 , Calculation
 , Proof, displayProof
 , showProofs
 , labelAsProven
 ) where

import Utilities
import LexBase
import AST
import TermZipper
import Binding
import Laws
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We consider a proof as being a transcript of the steps taken
to get from an initial goal to a final succesful outcome.

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
  \newpage
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

\newpage
\subsection{Proof Calculations}

We will represent proofs as
a straight calculation from the starting assertion
associated with the initial strategy
to the corresponind final assertion.
We also record any movements between hypotheses and consequents
during the proof.
We need to have an AST zipper to allow sub-terms to be singled out
for match and replace,
and some way of recording what happened,
so that proofs (complete or partial) can be saved,
restored, and reviewed.

The actions involved in a proof calculation step are as follows:
\begin{itemize}
  \item Select sub-term
  (which could be in either consequent, or any hypothesis).
  \item Match against laws.
  \item Select preferred match and apply its replacement.
  \item Record step (which subterm, which law).
\end{itemize}

Here we define a proof `record',
that records all the steps of the proof
in enough detail to allow the proof to be replayed.
The replay will require the same theory context as was used to
generate the proof.

There are two ways laws can be used to replace
a goal (sub-)term:
\begin{description}
  \item[matching]
    the sub-term is matched against part (or all) of the law,
    and is replaced by the other part (or $\true$).
  \item[instantiation]
     the sub-term is $\true$,
     and is replaced by the entire law
\end{description}
In both cases the match binding is used to build the replacement term.
First, a type that states how a law was used in a step:
\begin{code}
data HowUsed
  = ByMatch          -- replace focus with binding(match)
  | ByInstantiation  -- replace focus=true with binding(law)
  deriving (Eq,Show,Read)
\end{code}

The justification of a step records details of that step,
sufficient both to document the step for the reader,
and to be able to mechanically reply that step, or reverse it.
\begin{code}
data Justification
  = UseLaw
      HowUsed     -- how law was used in proof step
      String      -- law name
      Binding     -- binding from law variables to goal components
      [Int]       -- zipper descent arguments
  | Switch      -- switched focus at sequent level
      SeqFocus    -- focus before switch -- needed to reverse this.
      SeqFocus    -- focus after switch
  | CloneH Int  --  Cloned hypothesis i
  | Associate   -- grouped part of a flat use of an associative operator
      Identifier  -- operator
      GroupSpec   -- grouping details.
  deriving (Eq,Show,Read)
\end{code}

We make use of the following auxilliary types:
\begin{code}
data SeqFocus = CLeft | CRight | Hyp Int deriving (Eq,Show,Read)
\end{code}

Often it is worth knowing if a switch has occurred.
\begin{code}
isSequentSwitch :: Justification -> Bool
isSequentSwitch (Switch _ _)  =  True
isSequentSwitch _             =  False

justSwitched :: [CalcStep] -> Bool
justSwitched []         =  True -- starting a proof is considered a 'switch'
justSwitched ((j,_):_)  =  isSequentSwitch j
\end{code}

A calculation step records a justification,
plus the term that was present before the step occurred.
\begin{code}
type CalcStep
  = ( Justification  -- step justification
    , Term )         -- previous term
\end{code}

A calculation is the current term, plus all previous steps.
\begin{code}
type Calculation
  = ( Term -- end (or current) term
    , [ CalcStep ] )  -- calculation steps, in proof order
\end{code}

A proof has a name
(same as that of the orginating conjecture),
the assertion, a string denoting a known strategy,
and the relevant calculation.
\begin{code}
type Proof
  = ( String -- assertion name
    , Assertion
    , String -- Strategy
    , Calculation -- Simple calculational proofs for now
    )

labelAsProven :: NmdAssertion -> Proof -> Law
labelAsProven nasn (prfnm,_,_,_) =  (nasn, Proven prfnm)
\end{code}

\newpage
\subsection{Showing Proofs}

\textbf{This should all be done via proper generic rendering code}

\begin{code}
showJustification :: Justification -> String
showJustification (UseLaw how lnm bind dpath)
  =  "   = '"++showHow how++" "++lnm++"@" ++ show dpath ++ "'"
showJustification (Switch from to)
  =  "   [switch "++showSeqFocus from++" > "++showSeqFocus to++"]"
showJustification (CloneH i)
  =  "   [clone hypothesis "++show i++"]"
showJustification (Associate i gs)
  =  "   ["++showGroupSpec gs++" over "++trId i++"]"

showHow :: HowUsed -> String
showHow ByMatch = "match"
showHow ByInstantiation = "instantiate"

showSeqFocus :: SeqFocus -> String
showSeqFocus CLeft = "left"
showSeqFocus CRight = "right"
showSeqFocus (Hyp i) = "hyp. "++show i
\end{code}

\begin{code}
displayProof :: Proof -> String
displayProof (pnm,(trm,sc),strat,(trm',steps))
 = unlines' ( (pnm ++ " : " ++ trTerm 0 trm ++ " " ++ trSideCond sc)
              : ("by '"++strat++"'")
              : "---"
              : ( map shStep steps )
              ++ [trTerm 0 trm'] )

shStep :: CalcStep -> String
shStep ( (UseLaw how lnm bind dpath), trm )
   = unlines' [ trTermZip $ pathTZ dpath trm
              , " = '" ++ showHow how++" "++lnm++" @" ++ show dpath ++ "'"
              , trBinding bind
              ]
shStep ( just,  t )  =  unlines' [trTerm 0 t, showJustification just]
\end{code}


Showing Proofs:
\begin{code}
showProof (pnm,(trm,sc),strat,(trm',steps))
 = " " ++ pnm ++ "  (" ++ strat ++ ", size:" ++ show (length steps) ++ ")"

showProofs []      =  "No Proofs yet."
showProofs proofs
  =  unlines (
       "\nCompleted Proofs:"
       : map showProof proofs )
\end{code}
