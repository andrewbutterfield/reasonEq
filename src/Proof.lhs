\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proof
 ( TheLogic(..), flattenTheEquiv
 , Assertion, NmdAssertion, Provenance, Law
 , labelAsAxiom, labelAsProven
 , Theory(..), Sequent(..)
 , availableStrategies
 , Sequent'(..), SeqZip
 , leftConjFocus, rightConjFocus, hypConjFocus, exitSeqZipper
 , upSZ, downSZ
 , seqGoLeft, seqGoRight, switchLeftRight
 , seqGoHyp, seqLeaveHyp
 , getHypotheses
 , HowUsed(..)
 , Match(..)
 , Justification(..), isSequentSwitch, justSwitched
 , CalcStep
 , Calculation
 , LiveProof(..)
 , conjName__, conjName_, conjecture__, conjecture_, conjSC__, conjSC_
 , strategy__, strategy_, mtchCtxts__, mtchCtxts_, focus__, focus_
 , fPath__, fPath_, matches__, matches_, stepsSoFar__, stepsSoFar_
 , dispLiveProof
 , Proof, displayProof
 , startProof, launchProof
 , displayMatches
 , buildMatchContext, matchInContexts
 , proofComplete, finaliseProof
 , showLogic, showTheories, showNmdAssns, showLaws, showLivePrf, showProofs
 , numberList
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe
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
such as the notion of assertions, proof strategies,
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

\subsection{Logic}

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

\newpage
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
\subsection{Theories}

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
  | Proven Proof     -- demonstrated by proof
  deriving (Eq,Show,Read)

type Law = (NmdAssertion,Provenance)

labelAsAxiom :: NmdAssertion -> Law
labelAsAxiom  nasn  =  (nasn, Axiom)

labelAsProven :: NmdAssertion -> Proof -> Law
labelAsProven nasn prf =  (nasn, Proven prf)
\end{code}

A theory is a collection of laws linked
to information about which variables in those laws are deemed as ``known''.
\begin{code}
data Theory
  = Theory {
      thName :: String -- always nice to have one
    , laws   :: [Law]
    , knownV :: VarTable
    }
  deriving (Eq,Show,Read)
\end{code}




\subsection{Sequents}

A sequent is a collection containing
(i) $\mathcal L$ and $\mathcal H$ as a list of theories
(ii) a conjecture side-condition,
and (iii) and a pair of left and right conjecture-terms.
$$  \mathcal L,\mathcal H
    \vdash C_{left} \equiv C_{right}
    \qquad (s.c.)
$$
We will single out the hypothesis theory for special treatment.
\begin{code}
data Sequent
  = Sequent {
     ante :: [Theory] -- antecedent theory context
   , hyp :: Theory -- the goal hypotheses -- we can "go" here
   , sc :: SideCond -- of the conjecture being proven.
   , cleft :: Term -- never 'true' to begin with.
   , cright :: Term -- often 'true' from the start.
   }
  deriving (Eq, Show, Read)
\end{code}

\newpage
\subsubsection{Sequent Strategies}

Given any conjecture (named assertion)
we want to determine which strategies apply
and provide a choice of sequents.
We first flatten the implication (if any),
\begin{code}
availableStrategies :: TheLogic -> [Theory] -> NmdAssertion
                    -> [(String,Sequent)]
availableStrategies theLogic thys (nm,(tconj,sc))
  = catMaybes
     [ reduce  theLogic thys cflat
     , redboth theLogic thys cflat
     , assume  theLogic thys cflat ]
  where cflat = (nm,(flattenTheImp theLogic tconj,sc))
\end{code}
and then use the following functions to produce a sequent, if possible.

\begin{eqnarray*}
   reduce(C)
   &\defs&
   \mathcal L \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
reduce :: Monad m => TheLogic -> [Theory] -> NmdAssertion
       -> m (String, Sequent)
reduce logic thys (nm,(t,sc))
  = return ( "reduce", Sequent thys hthry sc t $ theTrue logic )
  where hthry = Theory ("H."++nm) [] $ makeUnknownKnown thys t
\end{code}

\begin{eqnarray*}
   redboth(C_1 \equiv C_2)
   &\defs&
   \mathcal L \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
redboth :: Monad m => TheLogic -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
redboth logic thys (nm,(t@(Cons tk i [tl,tr]),sc))
  | i == theEqv logic
      = return ( "redboth", Sequent thys hthry sc tl tr )
  where hthry = Theory ("H."++nm) [] $ makeUnknownKnown thys t
redboth logic thys (nm,(t,sc)) = fail "redboth not applicable"
\end{code}

\begin{eqnarray*}
   assume(H \implies C)
   &\defs&
   \mathcal L,\splitand(H) \vdash (C \equiv \true)
\end{eqnarray*}
\begin{code}
assume :: Monad m => TheLogic -> [Theory] -> NmdAssertion
       -> m (String, Sequent)
assume logic thys (nm,(t@(Cons tk i [ta,tc]),sc))
  | i == theImp logic
    = return ( "assume", Sequent thys hthry sc tc $ theTrue logic )
  where
    hlaws = map mkHLaw $ zip [1..] $ splitAnte logic ta
    mkHLaw (i,trm) = labelAsAxiom ("H."++nm++"."++show i,(trm,scTrue))
    hthry = Theory ("H."++nm) hlaws $ makeUnknownKnown thys t
assume _ _ _ = fail "assume not applicable"

splitAnte :: TheLogic -> Term -> [Term]
splitAnte theLogic (Cons tk i ts)
 | i == theAnd theLogic  =  ts
splitAnte _        t     =  [t]
\end{code}

\begin{eqnarray*}
   asmboth(H \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\splitand(H) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
asmboth :: Monad m => TheLogic -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
asmboth logic thys (nm,(t,sc)) = fail "asmboth not applicable"
\end{code}

\begin{eqnarray*}
   shunt(H_1 \implies \dots H_m \implies C)
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
shunt :: Monad m => TheLogic -> [Theory] -> NmdAssertion
      -> m (String, Sequent)
shunt logic thys (nm,(t,sc)) = fail "shunt not applicable"
\end{code}

\begin{eqnarray*}
   shntboth(H_1 \implies \dots H_m \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
shntboth :: Monad m => TheLogic -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
shntboth logic thys (nm,(t,sc)) = fail "shntboth not applicable"
\end{code}

\begin{eqnarray*}
   \splitand(H_1 \land \dots \land H_n)
   &\defs&
   \setof{H_1,\dots,H_n}
\end{eqnarray*}
\begin{code}
splitAnd :: TheLogic -> Term -> [Term]
splitAnd logic (Cons _ i ts)
  | i == theAnd logic  =  ts
splitAnd _ t           =  [t]
\end{code}

\newpage
\subsubsection{Making Unknown Variables Known}

A key function is one that makes all unknown variables in a term become known.
\begin{code}
makeUnknownKnown :: [Theory] -> Term -> VarTable
makeUnknownKnown thys t
  = let
     fvars = S.toList $ freeVars t
     vts = map knownV thys
    in scanFreeForUnknown vts newVarTable fvars

scanFreeForUnknown :: [VarTable] -> VarTable -> VarList -> VarTable
scanFreeForUnknown _ vt [] = vt
scanFreeForUnknown vts vt (StdVar v:rest)
  = scanFreeForUnknown vts (checkVarStatus vts vt v) rest
scanFreeForUnknown vts vt (LstVar lv:rest)
  = scanFreeForUnknown vts (checkLVarStatus vts vt lv) rest

checkVarStatus :: [VarTable] -> VarTable -> Variable -> VarTable
checkVarStatus vts vt v
  = case lookupVarTables vts v of
      UnknownVar
       -> case addKnownVar v ArbType vt of
            Nothing   ->  vt -- best we can do --- shouldn't happen?
            Just vt'  ->  vt'
      _               ->  vt

checkLVarStatus :: [VarTable] -> VarTable -> ListVar -> VarTable
checkLVarStatus vts vt (LVbl v _ _)
  = case lookupLVarTables vts v of
      UnknownListVar
       -> case addAbstractVarList v vt of
            Nothing   ->  vt -- best we can do --- shouldn't happen?
            Just vt'  ->  vt'
      _               ->  vt
\end{code}

\newpage
\subsection{Sequent Zipper}

We will need a zipper for sequents (and ante) as we can focus in on any term
in \texttt{hyp}, \texttt{cleft} or \texttt{cright}.

\subsubsection{Sequent Zipper Algebra}

The sequent type can be summarised algebraically as
\begin{eqnarray*}
   S &=& T^* \times T \times SC \times t \times t
\\ T &=& N \times L^* \times VD
\\ L &=& N \times (t \times SC) \times P
\end{eqnarray*}
where $T$ is \texttt{Theory},
$VD$ is \texttt{VarData},
$L$ is \texttt{Law},
$N$ is \texttt{Name},
$SC$ is \texttt{SideCond},
$P$ is \texttt{Provenance},
and $t$ is \texttt{Term}.

Re-arranging:
\begin{eqnarray*}
  && T^* \times T \times SC \times t \times t
\\&=&\textrm{Gathering terms independent of $t$ (we don't want to `enter' ` $T^*$)}
\\&& T^* \times SC \times T \times t^2
\\&=&\textrm{Expanding $T$}
\\&& T^* \times SC \times (N \times L^* \times VD) \times t^2
\\&=&\textrm{Expanding $L$}
\\&& T^* \times SC \times (N \times (N \times (t \times SC)\times P)^* \times VD) \times t^2
\\&=&\textrm{Flattening, re-arranging}
\\&& T^* \times SC \times N \times VD \times (N \times SC \times P \times t)^* \times t^2
\\&=&\textrm{Flattening, re-arranging}
\\&& A_1 \times (A_2 \times t)^* \times t^2
\end{eqnarray*}
where
\begin{eqnarray*}
   A_1  &=& T^* \times SC \times N \times VD
\\ A_2 &=& N \times SC \times P
\end{eqnarray*}

Differentiating:
\begin{eqnarray*}
   dS(t) \over dt
   &=&  d(A_1 \times (A_2 \times t)^* \times t^2) \over dt
\\ &=&  A_1 \times \left(~
                      (A_2 \times t)^* \times {d(t^2) \over dt}
                      +
                      t^2 \times { d((A_2 \times t)^*) \over dt}
                  ~\right)
\\ &=&  A_1 \times \left(~
                      (A_2 \times t)^* \times \mathbf{2} \times t
                      +
                      t^2 \times { d(A_2 \times t)^* \over d(A_2 \times t)}
                          \times { d(A_2 \times t) \over dt}
                  ~\right)
\\ &=&  A_1 \times \left(~
                      (A_2 \times t)^* \times \mathbf{2} \times t
                      +
                      t^2 \times ((A_2 \times t)^*)^2
                          \times A_2
                  ~\right)
\\
\\ S'(t) &=&  A_1 \times (A_2 \times t)^* \times \mathbf{2} \times t
\\ & &  +
\\ &=&  A_1 \times (A_2 \times t)^* \times A_2 \times (A_2 \times t)^*
            \times t^2
\end{eqnarray*}

We now refactor this by expanding the $A_i$ and merging
\begin{eqnarray*}
  && A_1 \times (A_2 \times t)^* \times \mathbf{2} \times t
     \quad+\quad
     A_1 \times (A_2 \times t)^* \times A_2 \times (A_2 \times t)^* \times t^2
\\&=&\textrm{Expand $A_2$}
\\&& A_1 \times (N \times SC \times P \times t)^* \times \mathbf{2} \times t
   \quad+\quad
   A_1 \times (N \times SC \times P \times t)^*
       \times N \times SC \times P
       \times (N \times SC \times P \times t)^*
       \times t^2
\\&=&\textrm{Fold instances of  $L$}
\\&& A_1 \times L^* \times \mathbf{2} \times t
   \quad+\quad
   A_1 \times L^* \times N \times SC \times P \times L^* \times t^2
\\&=&\textrm{Expand $A_1$}
\\&& T^* \times SC \times N \times VD \times L^* \times \mathbf{2} \times t
   \quad+\quad
   T^* \times SC \times N \times VD \times L^* \times N \times SC \times P \times L^* \times t^2
\\&=&\textrm{Fold instance of  $T$}
\\&& T^* \times SC \times T \times \mathbf{2} \times t
   \quad+\quad
   T^* \times SC \times N \times VD \times L^* \times N \times SC \times P \times L^* \times t^2
\\&=&\textrm{Common factor}
\\&& T^* \times SC \times
   \left(\quad
          T \times \mathbf{2} \times t
          \quad+\quad
          N \times VD \times L^* \times N \times SC \times P \times L^* \times t^2
   \quad\right)
\end{eqnarray*}

\newpage
\subsubsection{Sequent Zipper Types}

We start with the top-level common part:
$$S'(t) = T^* \times SC \times ( {\cdots + \cdots} )$$
\begin{code}
data Sequent'
  = Sequent' {
      ante0 :: [Theory] -- context theories
    , sc0       :: SideCond -- sequent side-condition
    , laws'     :: Laws'
    }
  deriving (Eq,Show,Read)
\end{code}

Now, the two variations
\begin{eqnarray*}
  && T \times \mathbf{2} \times t
\\&& N \times VD \times L^* \times N \times SC \times P \times L^* \times t^2
\end{eqnarray*}
However, there is one wrinkle we need to allow for.
When we focus on a hypothesis, we must record it's initial value,
so that it can be restored to its position,
with the modified version added on at the end as a new hypothesis.
\begin{code}
data Laws'
  = CLaws' { -- currently focussed on conjecture component
      hyp0  :: Theory -- hypothesis theory
    , whichC :: LeftRight -- which term is in the focus
    , otherC :: Term  -- the term not in the focus
    }
  | HLaws' { -- currently focussed on hypothesis component
      hname     :: String -- hyp. theory name
    , hknown    :: VarTable
    , hbefore   :: [Law] -- hyp. laws before focus (reversed)
    , fhName    :: String -- focus hypothesis name
    , fhSC      :: SideCond -- focus hypothesis sc (usually true)
    , fhProv    :: Provenance -- focus hypothesis provenance (?)
    , hOriginal :: Term -- the original form of the focus hypothesis
    , hafter    :: [Law] -- hyp. laws after focus
    , cleft0    :: Term -- left conjecture
    , cright0   :: Term -- right conjecture
    }
  deriving (Eq,Show,Read)

data LeftRight = Lft | Rght deriving (Eq,Show,Read)
\end{code}

Given that $S$ is not recursive, then the zipper for $S$
will have a term-zipper as its ``focus'', and a single instance
of $S'$ to allow the one possible upward ``step''.
\begin{code}
type SeqZip = (TermZip, Sequent')
\end{code}

\subsubsection{Sequent Zipper Construction}


To create a sequent-zipper,
we have to state which term component we are focussing on.
For the left- and right- conjectures, this is easy:
\begin{code}
leftConjFocus :: Sequent -> SeqZip
leftConjFocus sequent
  = ( mkTZ $ cleft sequent
    , Sequent' (ante sequent)
               (sc sequent) $
               CLaws' (hyp sequent) Lft (cright sequent) )

rightConjFocus sequent
  = ( mkTZ $ cright sequent
    , Sequent' (ante sequent)
               (sc sequent) $
               CLaws' (hyp sequent) Rght (cleft sequent) )
\end{code}

\newpage
For a hypothesis conjecture, making the sequent-zipper
is a little more tricky:
\begin{code}
hypConjFocus :: Monad m => Int -> Sequent -> m SeqZip
hypConjFocus i sequent
  = do let (Theory htnm hlaws hknown) = hyp sequent
       (before,((hnm,(ht,hsc)),hprov),after) <- peel i hlaws
       return ( mkTZ ht
              , Sequent' (ante sequent)
                         (sc sequent) $
                         HLaws' htnm hknown
                                before hnm hsc hprov ht after
                                (cleft sequent) (cright sequent) )
\end{code}

\subsubsection{Sequent Zipper Destructor}

Exiting a zipper:
\begin{code}
exitSeqZipper :: SeqZip -> Sequent
exitSeqZipper (tz,sequent') = exitSQ (exitTZ tz) sequent'

exitSQ :: Term -> Sequent' -> Sequent
exitSQ t sequent'
  = let (hypT,cl,cr) = exitLaws t $ laws' sequent'
    in Sequent (ante0 sequent') hypT (sc0 sequent') cl cr

exitLaws :: Term -> Laws' -> (Theory, Term, Term)
exitLaws currT (CLaws' h0 Lft  othrC)  =  (h0, currT, othrC)
exitLaws currT (CLaws' h0 Rght othrC)  =  (h0, othrC, currT)
exitLaws currT  (HLaws' hnm hkn hbef fnm fsc fprov horig haft cl cr)
  =  ( Theory hnm
              ( reverse hbef
                ++ [((fnm,(horig,fsc)),fprov)]
                ++ haft
                ++ [((fnm,(currT,fsc)),fprov)] )
              hkn
     , cl, cr)
\end{code}

\subsubsection{Sequent Zipper Moves}

The usual up/down actions just invoke the corresponding \texttt{TermZip} action.
\begin{code}
upSZ :: SeqZip -> (Bool,SeqZip)
upSZ (tz,seq')  =  let (moved,tz') = upTZ tz in (moved,(tz',seq'))

downSZ :: Int -> SeqZip -> (Bool,SeqZip)
downSZ i (tz,seq')  =  let (moved,tz') = downTZ i tz in (moved,(tz',seq'))
\end{code}

However we also have switch actions that jump between the three top-level
focii.
Switching between $C_{left}$ and $C_{right}$ is easy:
\begin{code}
seqGoLeft :: SeqZip -> (Bool, SeqZip)
seqGoLeft sz@(_,Sequent' _ _ (CLaws' _ Lft _))  =  (False,sz) -- already Left
seqGoLeft sz = (True,leftConjFocus $ exitSeqZipper sz)

seqGoRight :: SeqZip -> (Bool, SeqZip)
seqGoRight sz@(_,Sequent' _ _ (CLaws' _ Rght _))  =  (False,sz) -- already Right
seqGoRight sz = (True,rightConjFocus $ exitSeqZipper sz)

switchLeftRight :: SeqZip -> (Bool, Justification, SeqZip)
switchLeftRight sz@(_,Sequent' _ _ (CLaws' _ Lft _)) -- already Left
  =  (True, SwRight, rightConjFocus $ exitSeqZipper sz)
switchLeftRight sz@(_,Sequent' _ _ (CLaws' _ Rght _)) -- already Right
  =  (True, SwLeft,  leftConjFocus $ exitSeqZipper sz)
switchLeftRight sz -- must be in hypothesis
  =  (False, error "switchLeftRight: in hypothesis!", sz)
\end{code}
Entering a $H_i$  from $C_{left}$ or $C_{right}$ is easy.
But once in, we need a special command to exit.
\begin{code}
seqGoHyp :: Int -> SeqZip -> (Bool, SeqZip)
seqGoHyp i sz@(_,Sequent' _ _ (HLaws' _ _ _ _ _ _ _ _ _ _))
  =  (False,sz)  -- can't change hypothesis while in one.
seqGoHyp i sz
  =  case hypConjFocus i $ exitSeqZipper sz of
       Nothing   ->  (False,sz) -- bad index
       Just sz'  ->  (True,sz')
\end{code}
When we leave, the revised hypothesis must be added in as a new one.
\begin{code}
seqLeaveHyp :: SeqZip -> (Bool, SeqZip)
seqLeaveHyp sz@(_,Sequent' _ _ (HLaws' _ _ _ _ _ _ _ _ _ _))
  =  (True,leftConjFocus $ exitSeqZipper sz)
seqLeaveHyp sz -- not in hypothesis
  =  (False,sz)
\end{code}

Pulling out the hypothesis theory from the sequent zipper:
\begin{code}
getHypotheses :: Sequent' -> Theory
getHypotheses seq' = getHypotheses' $ laws' seq'
getHypotheses' (CLaws' hyp _ _)  =  hyp
getHypotheses' (HLaws' hn hk hbef _ _ _ _ haft _ _)
  =  Theory hn (reverse hbef ++ haft) hk

\end{code}
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

We start with live proofs:
\begin{code}
data LiveProof
  = LP {
      conjName :: String -- conjecture name
    , conjecture :: Assertion -- assertion being proven
    , conjSC :: SideCond -- side condition
    , strategy :: String -- strategy
    , mtchCtxts :: [MatchContext] -- current matching contexts
    , focus :: SeqZip  -- current sub-term of interest
    , fPath :: [Int] -- current term zipper descent arguments
    , matches :: Matches -- current matches
    , stepsSoFar :: [CalcStep]  -- calculation steps so far, most recent first
    }
  deriving (Eq, Show, Read)

-- field modification boilerplate
conjName__ f lp = lp{ conjName = f $ conjName lp}
conjName_ = conjName__ . const
conjecture__ f lp = lp{ conjecture = f $ conjecture lp}
conjecture_ = conjecture__ . const
conjSC__ f lp = lp{ conjSC = f $ conjSC lp}
conjSC_ = conjSC__ . const
strategy__ f lp = lp{ strategy = f $ strategy lp}
strategy_ = strategy__ . const
mtchCtxts__ f lp = lp{ mtchCtxts = f $ mtchCtxts lp}
mtchCtxts_ = mtchCtxts__ . const
focus__ f lp = lp{ focus = f $ focus lp}
focus_ = focus__ . const
fPath__ f lp = lp{ fPath = f $ fPath lp}
fPath_ = fPath__ . const
matches__ f lp = lp{ matches = f $ matches lp}
matches_ = matches__ . const
stepsSoFar__ f lp = lp{ stepsSoFar = f $ stepsSoFar lp}
stepsSoFar_ = stepsSoFar__ . const

data Match
 = MT { mName ::  String     -- assertion name
      , mAsn  ::  Assertion  -- matched assertion
      , mBind ::  Binding    -- resulting binding
      , mRepl ::  Term       -- replacement term
      } deriving (Eq,Show,Read)

type Matches = [Match]

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
dispLiveProof :: LiveProof -> String
dispLiveProof liveProof
 = unlines'
     ( ( ("Proof for '"++red (conjName liveProof)
          ++"'  "++trSideCond (conjSC liveProof))
       : ("by "++(strategy liveProof))
       : " ..."
       : map shLiveStep (reverse (stepsSoFar liveProof))
       )
       ++
       ( displayMatches (matches liveProof)
         : [ underline "           "
           , dispSeqZip (focus liveProof)
           , "" ]
       ) )


dispSeqZip :: SeqZip -> String
dispSeqZip (tz,Sequent' _ sc conj')  =  unlines' $ dispConjParts tz sc conj'

dispConjParts tz sc (CLaws' hthry Lft rightC)
  =     [ "R-target = "++trTerm 0 rightC++"  "++trSideCond sc, "" ]
     ++ (dispHypotheses hthry)
        : [ _vdash ]
     ++ [trTermZip tz]

dispConjParts tz sc (CLaws' hthry Rght leftC)
  =     [ "L-target = "++trTerm 0 leftC++"  "++trSideCond sc]
     ++ (dispHypotheses hthry)
        : [ _vdash ]
     ++ [trTermZip tz]

dispConjParts tz sc seq'@(HLaws' hn hk hbef _ _ _ horig haft _ _)
  =     [ "Hypothesis: "++trTerm 0 horig++"  "++trSideCond sc]
     ++ (dispHypotheses $ getHypotheses' seq')
        : [ _vdash ]
     ++ [trTermZip tz]
  where
     hthry = Theory hn (reverse hbef ++ haft) hk

dispHypotheses hthry  =  numberList' showHyp $ laws $ hthry
showHyp ((_,(trm,_)),_) = trTerm 0 trm

dispTermZip :: TermZip -> String
dispTermZip tz = blue $ trTerm 0 (getTZ tz)

shLiveStep :: CalcStep -> String
shLiveStep ( just, trm )
  = unlines' [ trTerm 0 trm, showJustification just]

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

displayMatches :: Matches -> String
displayMatches []  =  ""
displayMatches matches
  =  unlines' ( ("Matches:") : map shMatch (zip [1..] matches))

shMatch (i, mtch)
 = ( show i ++ " : "++ ldq ++ green (mName mtch) ++ rdq
     ++ " gives     "
     ++ (bold . blue)
           ( trTerm 0 (fromJust $ instantiate bind $ mRepl mtch)
             ++ "  "
             ++ trSideCond (fromJust $ instantiateSC bind $ lsc) ) )
 where
    bind = mBind mtch
    (lt,lsc) = mAsn mtch
\end{code}

We then continue with a proof (record):
\begin{code}
type Proof
  = ( String -- assertion name
    , Assertion
    , String -- Strategy
    , Calculation -- Simple calculational proofs for now
    )

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
We need to setup a proof from a conjecture:
\begin{code}
startProof :: TheLogic -> [Theory] -> String -> Assertion -> LiveProof
startProof logic thys nm asn@(t,sc)
  =  LP { conjName = nm
        , conjecture = asn
        , conjSC = sc
        , strategy = strat
        , mtchCtxts =  mcs
        , focus =  sz
        , fPath = []
        , matches = []
        , stepsSoFar = []
        }
  where
    (strat,seq) = fromJust $ reduce logic thys (nm,asn)
    sz = leftConjFocus seq
    mcs = buildMatchContext thys
\end{code}

\begin{code}
launchProof :: [Theory] -> String -> Assertion -> (String,Sequent) -> LiveProof
launchProof thys nm asn@(t,sc) (strat,seq)
  = LP { conjName = nm
        , conjecture = asn
        , conjSC = sc
        , strategy = strat
        , mtchCtxts =  mcs
        , focus =  sz
        , fPath = []
        , matches = []
        , stepsSoFar = []
        }
  where
    sz = leftConjFocus seq
    hthy = hyp seq
    mcs = if null $ laws hthy
           then buildMatchContext thys
           else buildMatchContext (hthy:thys)
\end{code}
We need to determine when a live proof is complete:
\begin{code}
proofComplete :: TheLogic -> LiveProof -> Bool
proofComplete logic liveProof
  =  let
       sequent = exitSeqZipper $ focus liveProof
       hypTerms = map (fst . snd . fst) $ laws $ hyp sequent
     in cleft sequent == cright sequent -- should be alpha-equivalent
        ||
        any (== theFalse logic) hypTerms
\end{code}

We need to convert a complete live proof to a proof:
\begin{code}
finaliseProof :: LiveProof -> Proof
finaliseProof liveProof
  = ( conjName liveProof
    , conjecture liveProof
    , strategy liveProof
    , ( exitTZ $ fst $ focus liveProof
      , reverse $ stepsSoFar liveProof ) )
\end{code}

\newpage
\subsection{Matching Contexts}

Consider a collection of theories in an ordered list,
where each theory appears in that list before any of those on which
it depends.
Matching a conjecture component against all of these laws
means working through the theories, from first to last.
When working with a given theory, we want to match against
all the laws in that theory, using every variable-data table
in that theory and its dependencies.
In particular, if a pattern variable occurs in more than one var-table,
then we want the data from the first such table.

So given that we are matching in the context of a list of dependency-ordered
theories, we want to use a corresponding list of match contexts,
one for each theory.
A match context for a theory contains all the laws of that theory,
along with a dependency-ordered list of the var-tables,
including that of the theory itself,
as well as those from all subsequent theories.
\begin{code}
type MatchContext
  = ( [Law]        -- all laws of this theory
    , [VarTable] ) -- all known variables here, and in dependencies
\end{code}

Given a list of theories, we generate a list of match-contexts:
\begin{code}
buildMatchContext :: [Theory] -> [MatchContext]
buildMatchContext [] = []
buildMatchContext [thy] = [ (laws thy, [knownV thy]) ]
buildMatchContext (thy:thys)
  = let mcs'@((_,vts'):_) = buildMatchContext thys
    in (laws thy, knownV thy : vts') : mcs'
\end{code}

\newpage
\subsection{Assertion Matching}

First, given list of match-contexts, systematically work through them.
\begin{code}
matchInContexts :: TheLogic -> [MatchContext] -> Term -> Matches
matchInContexts logic mcs t
  = concat $ map (matchLaws logic t) mcs
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: TheLogic -> Term -> MatchContext -> Matches
matchLaws logic t (lws,vts) = concat $ map (domatch logic vts t) lws
\end{code}

For each law,
we check its top-level to see if it is an instance of \texttt{theEqv},
in which case we try matches against all possible variations.
\begin{code}
domatch :: TheLogic -> [VarTable] -> Term -> Law -> Matches
domatch logic vts tC ((n,asn@(tP@(Cons tk i ts@(_:_:_)),sc)),prov)
  | i == theEqv logic  =  concat $ map (eqvMatch vts tC) $ listsplit ts
  where
      -- tC :: equiv(tsP), with replacement equiv(tsR).
    eqvMatch vts tC (tsP,tsR)
      = justMatch (eqv tsR) vts tC ((n,(eqv tsP,sc)),prov)
    eqv []   =  theTrue logic
    eqv [t]  =  t
    eqv ts   =  Cons tk i ts
\end{code}
Otherwise we just match against the whole law.
\begin{code}
domatch logic vts tC law
 = justMatch (theTrue logic) vts tC law
\end{code}

Do a simple match:
\begin{code}
justMatch :: Term -> [VarTable] -> Term -> Law -> Matches
justMatch repl vts tC ((n,asn@(tP,_)),_)
 = case match vts tC tP of
     Nothing -> []
     Just bind -> [MT n asn bind repl]
\end{code}

\newpage
\subsection{Showing stuff}

\textbf{This should all be done via proper generic rendering code}

Showing logic:
\begin{code}
showLogic logic
  = unlines' [ "Truth: "   ++ trTerm 0 (theTrue logic)
             , "Equivalence: " ++ trId (theEqv  logic)
             , "Implication: " ++ trId (theImp  logic)
             , "Conjunction: " ++ trId (theAnd  logic) ]
\end{code}


A common idiom is to show a list of items as a numbered list
to make selecting them easier:
\begin{code}
numberList showItem list
  =  unlines' $ map (numberItem showItem) $  zip [1..] list
numberItem showItem (i,item)
  =  pad 4 istr ++ istr ++ ". " ++ showItem item
  where istr = show i

pad w str
  | ext > 0    =  replicate ext ' '
  | otherwise  =  ""
  where ext = w - length str
\end{code}

Sometimes, we want the number afterwards:
\begin{code}
numberList' showItem list
  = let
     lstrings = map showItem' list
     showItem' item = (istr,length istr) where istr = showItem item
     maxw = maximum $ map snd lstrings
    in unlines' $ map (numberItem' (maxw+2)) $ zip [1..] lstrings
numberItem' maxw (i,(str,strlen))
  = str ++ replicate (maxw-strlen) ' ' ++ pad 2 istr ++ istr
  where istr = show i
\end{code}

Showing theories:
\begin{code}
showTheories [] = "No theories present."
showTheories (thry:_)
  = unlines'
      [ "Theory (top) '"++thName thry++"'"
      , trVarTable (knownV thry)
      , showLaws (laws thry) ]

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
showProv (Proven _)  =  _subStr "P"
\end{code}

Showing Proof:
\begin{code}
showLivePrf Nothing = "no Proof."
showLivePrf (Just proof) = dispLiveProof proof
\end{code}

Showing Proofs:
\begin{code}
showProofs []      =  "No Proofs yet."
showProofs proofs  =  unlines' $ map ( ('\n':) . displayProof ) proofs
\end{code}
