\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proofs
 ( MatchClass
 , pattern MatchAll, pattern MatchEqv
 , pattern MatchAnte, pattern MatchCnsq
 , pattern MatchEqvVar
 , HowUsed(..)
 , SeqFocus(..), Justification(..), showJustification
 , isSequentSwitch, justSwitched
 , CalcStep, isStraightStep
 , Calculation, isStraightCalc
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

\emph{On notation: } we shall use lower-case letters $p,q,r,h,c,a$ to denote predicate
terms of arbitrary form,
and upper-case letters $P,Q,R$
to denote terms that are a single predicate (meta-)variable.

Consider a pre-existing set of laws $\mathcal L$ (axioms plus proven theorems),
and consider that we have a conjecture $c$ that we want to prove.
The most general proof framework we plan to support is the following:
\begin{description}
  \item[Deduction]
    In general we partition $c$ into three components:
    \begin{description}
      \item[Hypotheses]
        A set $\mathcal H = \setof{h_1,\dots,h_n}$ of hypotheses,
        for $n \geq 0$,
        in which all unknown variables in the $h_i$
        are temporarily marked as ``known'' (as themselves),
        for the duration of the proof.
      \item[Consequents]
        A pair of sub-conjectures $c_{left}$ and $c_{right}$.
    \end{description}
    We require these to be chosen such that:
    $$ c \quad
        =  \bigwedge_{i \in 1\dots n} h_i
              \implies (c_{left} \equiv c_{right})$$
    Our proof is the based upon the sequent:
    $$ \mathcal L,h_1,\dots,h_n \vdash c_{left} \equiv c_{right}$$
    where we use the laws in both $\mathcal L$ and $\mathcal H$
    to transform either or both
    of $c_{left}$ and $c_{right}$ until they are the same.
  \newpage
  \item[Calculation]
    We define two kinds of calculation steps:
    \begin{description}
      \item[standard]
        We use a law from $\mathcal L$ or $\mathcal H$
        to transform either sub-conjecture:
        \begin{eqnarray*}
           \mathcal L,\mathcal H &\vdash&  c_x
        \\ &=& \textrm{effect of some assertion $A$
                                      in $\mathcal L\cup \mathcal H$
                                      on (a sub-term of) $c_x$}
        \\ \mathcal L,\mathcal H &\vdash& c'_x
        \end{eqnarray*}
      \item[deductive]
        We select a hypothesis from in front of the turnstile,
        and use the laws and the rest of the hypotheses to transform it.
        We add the transformed version into the hypotheses,
        retaining its original form as well.
        \begin{eqnarray*}
           \mathcal L,\mathcal H &\vdash& c_x
        \\ &\downarrow& \textrm{select $h_i$}
        \\ \mathcal L,\mathcal H\setminus\setof{h_i}
           &\vdash& h_i
        \\ &=& \textrm{effect of some assertion $a$
                                      in $\mathcal L\cup \mathcal H\setminus\setof{H_i}$
                                      on $h_i$}
        \\ \mathcal L,\mathcal H\setminus\setof{h_i}
           &\vdash& h'_i
        \\ &\downarrow& \textrm{restore calculational sequent}
        \\ \mathcal L,\mathcal H\cup\setof{h_{n+1}} &\vdash& c_x \qquad h_{n+1} = h'_i
        \end{eqnarray*}
        We may do a number of calculational steps on $h_i$ before
        restoring the original standard sequent.
    \end{description}
\end{description}

There are a number of strategies we can apply, depending on the structure
of $c$, of which the following three are most basic
\begin{eqnarray*}
   reduce(c)
   &\defs&
   \mathcal L \vdash c \equiv \true
\\ redboth(c_1 \equiv c_2)
   &\defs&
   \mathcal L \vdash c_1 \equiv c_2
\\ assume(h \implies c)
   &\defs&
   \mathcal L,\splitand(h) \vdash (c \equiv \true)
\end{eqnarray*}
where
\begin{eqnarray*}
\\ \splitand(h_1 \land \dots \land h_n)
   &\defs&
   \setof{h_1,\dots,h_n}
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
to the corresponing final assertion.
We also record any movements between hypotheses and consequents
during the proof.
We need to have an AST zipper to allow sub-terms to be singled out
for match and replace,
and some way of recording what happened,
so that proofs (complete or partial) can be saved,
restored, and reviewed.

An assertion $a$ is a term/side-condition pair $(t,sc)$.
Consider that case of matching a candidate term and side-condition
$a_C =(t_C,sc_C)$
against a pattern term and side-conditions
$a_P =(t_P,sc_P)$.
Once we have a binding $\beta$,
we can apply it to the pattern side-condition
to translate it into candidate ``space'':
$$
sc_{P'} = \beta(sc_P).
$$
In order to discharge the pattern side-condition,
we must prove that the candidate side-conditions
are sufficient to infer the translated version
of the candidate side-condition:
$$
sc_C \implies sc_{P'}.
$$
In general, the candidate term $t_C$ will be a sub-part
(the ``focus'')
of a larger goal term $t_G$,
and the pattern $t_P$ may be part of a complete law $t_L$
(e.g., one side of an equivalence).
This can mean that sometimes we need to take this larger
context in mind.
This can also mean that the binding returned by matching is
incomplete and needs to be augmented in this larger context.

So the overall matching process is,
given $t_C$ and $t_P$ chosen from $t_G$ and $t_L$:
\begin{enumerate}
  \item match $t_C$ against $t_P$ to obtain binding $\beta_1$;
  \item complete bindings in the overall contexts
    determined by $a_G$ and $a_L$ to get $\beta_2$;
    \\ Note that, given existential conditions,
     this may require $sc_C$ to be extended to $sc'_C$.
  \item compute $sc'_P=\beta_2(sc_P)$;
  \item check validity of $sc'_C \implies sc'_P$;
  \item return $\beta_2$ as final result.
\end{enumerate}
This has the following implications for live proofs:
we need access to $a_G$ and $a_L$;
and we also need to record $sc'_C$ in every proof-step.



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

\subsubsection{Partial Matching}

Given a sub-term and a law-term
there may a number of different ways in which we can match
the sub-term against the law-term.
This depends on the top-level structure of the law-term,
which also determines how the match binding is used
to produce the replacement term.

The following table describes some examples of
how equivalences and implications
can admit matches against sub-parts.
$$\begin{array}{|c|c|c|c|c|c|}
\hline
 \mbox{match-type} & \mbox{law struct.} & \mbox{pattern}
 & \mbox{repl.}
 & \mbox{step rel.}
\\\hline
  \mbox{Full} & \mbox{any} & \mbox{all}
 & \true & \equiv
\\\hline
 \equiv\mbox{LHS} & p \equiv q & p
 & q\beta & \equiv
\\\hline
 \equiv\mbox{RHS} & p \equiv q & q
 & p\beta & \equiv
\\\hline
 \implies\mbox{ANTE} & p \implies q & p
 & (p \land q)\beta & \equiv
\\\hline
 \implies\mbox{ANTE} & p \implies q & p
 & q\beta & \implies
\\\hline
 \implies\mbox{CNSQ} & p \implies q & q
 & (q \lor p)\beta & \equiv
\\\hline
 \implies\mbox{CNSQ} & p \implies q & q
 & p\beta & \impliedby
\\\hline
\end{array}$$
We assume that $\beta$ is the binding returned by the match.

We can generalise the $p\equiv q$ law structure example above
to the more general $p_1 \equiv p_2 \equiv \dots \equiv p_n$,
where we might match against $p_1 \equiv \dots \equiv p_k$ (say),
with $(p_{k+1} \equiv \dots \equiv p_n)\beta$ as the replacement.
Similar generalisations apply to laws of the form
$p_1 \implies \dots \implies p_n \implies q$.

Finally, laws of the form $Complicated \equiv P$,
will always succeed, \emph{for any candidate}, in a $\equiv$RHS match,
with $Complicated\beta$ as a replacement.
These ``expanding'' matches can be useful from time to time,
but usually they are considered to be annoying.
These need to clearly identified.

\newpage
We shall define the following match partiality classes,
assuming that $n \geq 2$, $N = 1\dots n$ and $M \subset N$.
$$
\begin{array}{|c|c|c|c|}
  \hline
  \mbox{partial match class} & \mbox{law struct} & \mbox{patn.} & \mbox{repl.}
\\\hline
  \mbox{All} & p & p & \true
\\\hline
  \mbox{Eqv}(M)
  & \equiv_{i \in N} p_i
  & \equiv_{j \in M} p_j
  & \equiv_{k \in N\setminus M} p_k\beta
\\\hline
  \mbox{Ante}
  & a \implies c
  & a
  & (a \land c)\beta
\\\hline
  \mbox{Cnsq}
  & a \implies c
  & c
  & (c \lor a)\beta
\\\hline
  \mbox{EqvVar}(k), k \in N
  & \equiv_{i \in 1\dots n} p_i, p_k = P
  & P
  & \equiv_{j \in N\setminus\{k\}} p_j\beta
\\\hline
\end{array}
$$
So we have a match partiality class datatype:
\begin{code}
data MatchClass
  = MA       -- match all of law, with replacement 'true'
  | ME [Int] -- match subpart of 'equiv' chain
  | MIA      -- match implication antecedent A, replacement A /\ C
  | MIC      -- match implication consequent C, replacement A \/ C
  -- MEV should be last, so these matches rank low by default
  | MEV Int  -- match PredVar at given position
  deriving (Eq,Ord,Show,Read)

pattern MatchAll       = MA
pattern MatchEqv is    = ME is
pattern MatchAnte      = MIA
pattern MatchCnsq      = MIC
pattern MatchEqvVar i  = MEV i
\end{code}

Now, a type that states how a law was used in a step:
\begin{code}
data HowUsed
  = ByMatch MatchClass  -- replace focus with binding(match)
  | ByInstantiation     -- replace focus=true with binding(law)
  deriving (Eq,Show,Read)
\end{code}

The justification of a step records details of that step,
sufficient both to document the step for the reader,
and to be able to mechanically reply that step, or reverse it.
\textbf{
  Maybe we should have the focus path ([Int]) in all variants,
  as we would like to restore the previous focus
}
\begin{code}
data Justification
  = UseLaw             -- used a law
      HowUsed              -- how law was used in proof step
      String               -- law name
      Binding              -- binding from law variables to goal components
      [Int]                -- zipper descent arguments
  | Switch             -- switched focus at sequent level
      SeqFocus             -- focus before switch -- needed to reverse this.
      SeqFocus             -- focus after switch
  | CloneH Int         --  Cloned hypothesis i
  | Flatten Identifier -- flattened use of associative operator
  | Associate          -- grouped use of an associative operator
      Identifier           -- operator
      GroupSpec            -- grouping details.
  deriving (Eq,Show,Read)
\end{code}

We make use of the following auxilliary types:
\begin{code}
data SeqFocus = CLeft | CRight | Hyp Int deriving (Eq,Show,Read)
\end{code}

A simple or straight calculation is one that does not change
the part of the sequent being manipulated,
\textit{i.e.}, is not a switch or clone:
\begin{code}
isStraightJ :: Justification -> Bool
isStraightJ (Switch _ _)  =  False
isStraightJ (CloneH _)    =  False
isStraightJ _             =  True
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
    , Assertion )         -- previous term

isStraightStep :: CalcStep -> Bool
isStraightStep ( j, _ ) = isStraightJ j
\end{code}

A calculation is the current term, plus all previous steps.
\begin{code}
type Calculation
  = ( Term -- end (or current) term
    , [ CalcStep ] )  -- calculation steps, in proof order

isStraightCalc :: Calculation -> Bool
isStraightCalc ( _, calc ) = all isStraightStep calc
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
  =  "   = '"++showHow how++" "++nicelawname lnm++"@" ++ show dpath ++ "'"
showJustification (Switch from to)
  =  "   [switch "++showSeqFocus from++" > "++showSeqFocus to++"]"
showJustification (CloneH i)
  =  "   [clone hypothesis "++show i++"]"
showJustification (Flatten i)
  =  "   [flatten "++trId i++"]"
showJustification (Associate i gs)
  =  "   ["++showGroupSpec gs++" over "++trId i++"]"

showHow :: HowUsed -> String
showHow (ByMatch mc) = showMatchClass mc
showHow ByInstantiation = "instantiate"

showMatchClass :: MatchClass -> String
showMatchClass MatchAll         =  "match-all"
showMatchClass (MatchEqv is)    =  "match-equiv"++show is
showMatchClass MatchAnte        =  "match-ante"
showMatchClass MatchCnsq        =  "match-cnsq"
showMatchClass (MatchEqvVar i)  =  "match-eqv-pvar("++show i++")"

showSeqFocus :: SeqFocus -> String
showSeqFocus CLeft = "left"
showSeqFocus CRight = "right"
showSeqFocus (Hyp i) = "hyp. "++show i
\end{code}

\begin{code}
displayProof :: Proof -> String
displayProof (pnm,asn,strat,(trm',steps))
 = unlines' ( (pnm ++ " : " ++ trAsn asn)
              : ("by '"++strat++"'")
              : "---"
              : ( map shStep steps )
              ++ [trTerm 0 trm'] )

shStep :: CalcStep -> String
shStep ( (UseLaw how lnm bind dpath), asn@(trm,sc) )
   = unlines' [ trTermZip (pathTZ dpath trm) ++ trSC sc
              , " = '" ++ showHow how++" "++lnm++" @" ++ show dpath ++ "'"
              , trBinding bind
              ]
   where
     trSC [] = ""
     trSC sc = " ,  "++trSideCond sc
shStep ( just, asn )  =  unlines' [ trAsn asn
                                  , showJustification just ]
\end{code}


Showing Proofs:
\begin{code}
showProof (pnm,(trm,sc),strat,(trm',steps))
 = " " ++ pnm ++ "  (" ++ strat ++ ", size:" ++ show (length steps) ++ ")"

showProofs _ []      =  "No Proofs yet."
showProofs [nm] proofs = listProofs nm proofs
showProofs _ proofs
  =  unlines (
       "\nCompleted Proofs (true names):"
       : map showProof proofs )

listProofs _ [] = "No such proof"
listProofs nm (prf@(pnm,_,_,_):rest)
  | nm == pnm  =  displayProof prf
  | otherwise  =   listProofs nm rest

listProof (pnm,(trm,sc),strat,(trm',steps))
 = "listProof NYI"
\end{code}
