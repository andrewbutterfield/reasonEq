\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proof
 ( TheLogic(..), flattenTheEquiv
 , Assertion, Law, Theory(..), Sequent(..)
 , availableStrategies
 , SeqZip
 , leftConjFocus, rightConjFocus, hypConjFocus, exitSeqZipper
 , upSZ, downSZ, seqGoLeft, seqGoRight, seqGoHyp
 , Justification
 , CalcStep
 , Calculation
 , LiveProof, dispLiveProof
 , Proof, displayProof
 , startProof, launchProof
 , displayMatches
 , buildMatchContext, matchInContexts
 , proofComplete, finaliseProof
 , showLogic, showTheories, showLaws, showLivePrf, showProofs
 , numberList
 ) where

-- import Data.Set (Set)
-- import qualified Data.Set as S
import Data.Maybe
--
import Utilities
import LexBase
-- import Variables
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
of truth, logical equivalence, implication and conjunctions.
$$ \true \qquad \equiv \qquad \implies \qquad \land $$
\begin{code}
data TheLogic
  = TheLogic
     { theTrue :: Term
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

Laws always have names, so a law is a named-assertion:
\begin{code}
type Law = (String,Assertion)
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

\subsubsection{Sequent Strategies}

Given any conjecture we want to determine which strategies apply
and provide a choice of sequents.
We first flatten the implication (if any),
\begin{code}
availableStrategies :: TheLogic -> [Theory] -> (String,Assertion) -> [Sequent]
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
reduce :: Monad m => TheLogic -> [Theory] -> (String,Assertion) -> m Sequent
reduce logic thys (nm,(t,sc))
  = return $ Sequent thys hthry sc t $ theTrue logic
  where hthry = Theory ("H."++nm) [] $ makeUnknownKnown thys t
\end{code}

\begin{eqnarray*}
   redboth(C_1 \equiv C_2)
   &\defs&
   \mathcal L \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
redboth :: Monad m => TheLogic -> [Theory] -> (String,Assertion) -> m Sequent
redboth logic thys (nm,(t@(Cons tk i [tl,tr]),sc))
  | i == theEqv logic
      = return $ Sequent thys hthry sc tl tr
  where hthry = Theory ("H."++nm) [] $ makeUnknownKnown thys t
redboth logic thys (nm,(t,sc)) = fail "redboth not applicable"
\end{code}

\begin{eqnarray*}
   assume(H \implies C)
   &\defs&
   \mathcal L,\splitand(H) \vdash (C \equiv \true)
\end{eqnarray*}
\begin{code}
assume :: Monad m => TheLogic -> [Theory] -> (String,Assertion) -> m Sequent
assume logic thys (nm,(t@(Cons tk i [ta,tc]),sc))
  | i == theImp logic
    = return $ Sequent thys hthry sc tc $ theTrue logic
  where
    hlaws = map mkHLaw $ zip [1..] $ splitAnte logic ta
    mkHLaw (i,t) = ("H."++nm++"."++show i,(t,scTrue))
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
asmboth :: Monad m => TheLogic -> [Theory] -> (String,Assertion) -> m Sequent
asmboth logic thys (nm,(t,sc)) = fail "asmboth not applicable"
\end{code}

\begin{eqnarray*}
   trade(H_1 \implies \dots H_m \implies C)
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
trade :: Monad m => TheLogic -> [Theory] -> (String,Assertion) -> m Sequent
trade logic thys (nm,(t,sc)) = fail "trade not applicable"
\end{code}

\begin{eqnarray*}
   trdboth(H_1 \implies \dots H_m \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
trdboth :: Monad m => TheLogic -> [Theory] -> (String,Assertion) -> m Sequent
trdboth logic thys (nm,(t,sc)) = fail "trdboth not applicable"
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

\subsection{Making Unknown Variables Known}

A key function is one that makes all unknown variables in a term become known.
\begin{code}
makeUnknownKnown :: [Theory] -> Term -> VarTable
makeUnknownKnown thys t = newVarTable -- for now.....
\end{code}

\subsection{Sequent Zipper}

We will need a zipper for sequents (and ante) as we can focus in on any term
in \texttt{hyp}, \texttt{cleft} or \texttt{cright}.

\subsubsection{Sequent Zipper Algebra}

The sequent type can be summarised algebraically as
\begin{eqnarray*}
   S &=& T^* \times T \times SC \times t \times t
\\ T &=& N \times L^* \times VD
\\ L &=& N \times (t \times SC)
\end{eqnarray*}
where $T$ is \texttt{Theory},
$VD$ is \texttt{VarData},
$L$ is \texttt{Law},
$N$ is \texttt{Name},
$SC$ is \texttt{SideCond},
and $t$ is \texttt{Term}.

Re-arranging:
\begin{eqnarray*}
  && T^* \times T \times SC \times t \times t
\\&=&\textrm{Gathering terms independent of $t$ (we don't want to `enter' ` $T^*$)}
\\&& T^* \times SC \times T \times t^2
\\&=&\textrm{Expanding $T$}
\\&& T^* \times SC \times (N \times L^* \times VD) \times t^2
\\&=&\textrm{Expanding $L$}
\\&& T^* \times SC \times (N \times (N \times (t \times SC))^* \times VD) \times t^2
\\&=&\textrm{Flattening, re-arranging}
\\&& T^* \times SC \times N \times VD \times (N \times SC \times t)^* \times t^2
\\&=&\textrm{Flattening, re-arranging}
\\&& A_1 \times (A_2 \times t)^* \times t^2
\end{eqnarray*}
where
\begin{eqnarray*}
   A_1  &=& T^* \times SC \times N \times VD
\\ A_2 &=& N \times SC
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
\\&& A_1 \times (N \times SC \times t)^* \times \mathbf{2} \times t
   \quad+\quad
   A_1 \times (N \times SC \times t)^* \times N \times SC \times (N \times SC \times t)^* \times t^2
\\&=&\textrm{Fold instances of  $L$}
\\&& A_1 \times L^* \times \mathbf{2} \times t
   \quad+\quad
   A_1 \times L^* \times N \times SC \times L^* \times t^2
\\&=&\textrm{Expand $A_1$}
\\&& T^* \times SC \times N \times VD \times L^* \times \mathbf{2} \times t
   \quad+\quad
   T^* \times SC \times N \times VD \times L^* \times N \times SC \times L^* \times t^2
\\&=&\textrm{Fold instance of  $T$}
\\&& T^* \times SC \times T \times \mathbf{2} \times t
   \quad+\quad
   T^* \times SC \times N \times VD \times L^* \times N \times SC \times L^* \times t^2
\\&=&\textrm{Common factor}
\\&& T^* \times SC \times
   \left(\quad
          T \times \mathbf{2} \times t
          \quad+\quad
          N \times VD \times L^* \times N \times SC \times L^* \times t^2
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
  deriving (Show,Read)
\end{code}

Now, the two variations
\begin{eqnarray*}
  && T \times \mathbf{2} \times t
\\&& N \times VD \times L^* \times N \times SC \times L^* \times t^2
\end{eqnarray*}
\begin{code}
data Laws'
  = CLaws' { -- currently focussed on conjecture component
      hyp0  :: Theory -- hypothesis theory
    , whichC :: LeftRight -- which term is in the focus
    , otherC :: Term  -- the term not in the focus
    }
  | HLaws' { -- currently focussed on hypothesis component
      hname :: String -- hyp. theory name
    , hknown :: VarTable
    , hbefore :: [Law] -- hyp. laws before focus (reversed)
    , fhName  :: String -- focus hypothesis name
    , fhSC    :: SideCond -- focus hypothesis sc (usually true)
    , hafter  :: [Law] -- hyp. laws after focus
    , cleft0  :: Term -- left conjecture
    , cright0 :: Term -- right conjecture
    }
  deriving (Show,Read)

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
       (before,(hnm,(ht,hsc)),after) <- peel i hlaws
       return ( mkTZ ht
              , Sequent' (ante sequent)
                         (sc sequent) $
                         HLaws' htnm hknown
                                before hnm hsc after
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
exitLaws currT  (HLaws' hnm hkn hbef fnm fsc haft cl cr)
  =  (Theory hnm (reverse hbef ++ (fnm,(currT,fsc)) : haft) hkn, cl, cr)
\end{code}

\subsubsection{Sequent Zipper Moves}

The usual up/down actions just invoke the corresponding \texttt{TermZip} action.
\begin{code}
upSZ :: SeqZip -> (Bool,SeqZip)
upSZ (tz,seq')  =  let (moved,tz') = upTZ tz in (moved,(tz',seq'))

downSZ :: Int -> SeqZip -> (Bool,SeqZip)
downSZ i (tz,seq')  =  let (moved,tz') = downTZ i tz in (moved,(tz',seq'))
\end{code}

However we also have a switch action that jumps between the three top-level
focii.
\begin{code}
seqGoLeft :: SeqZip -> (Bool, SeqZip)
seqGoLeft sz@(_,Sequent' _ _ (CLaws' _ Lft _))  =  (False,sz) -- already Left
seqGoLeft sz = (True,leftConjFocus $ exitSeqZipper sz)

seqGoRight :: SeqZip -> (Bool, SeqZip)
seqGoRight sz@(_,Sequent' _ _ (CLaws' _ Rght _))  =  (False,sz) -- already Right
seqGoRight sz = (True,rightConjFocus $ exitSeqZipper sz)

seqGoHyp :: Int -> SeqZip -> (Bool, SeqZip)
seqGoHyp i sz@(_,Sequent' _ _ (HLaws' _ _ bef _ _ _ _ _))
                           | i+1 == length bef  =  (False,sz) -- already at ith.
seqGoHyp i sz
  =  case hypConjFocus i $ exitSeqZipper sz of
       Nothing   ->  (False,sz) -- bad index
       Just sz'  ->  (True,sz')
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

The actions involed in a proof calculation step are as follows:
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
type LiveProof
  = ( String -- conjecture name
    , Assertion -- assertion being proven
    , SideCond -- side condition
    , [MatchContext] -- current matching contexts
    , SeqZip  -- current term, focussed
    , [Int] -- current zipper descent arguments (cleft,cright,hyp=1,2,3)
    , Matches -- current matches
    , [CalcStep]  -- calculation steps so far, most recent first
    )

atCleft   =  [1]
atCright  =  [2]
atHyp i   =  [3,i]

type Match
 = ( String -- assertion name
   , Assertion -- matched assertion
   , Binding -- resulting binding
   , Term  -- replacement
   )

type Matches
  = [ ( Int -- match number
      , Match ) ]  -- corresponding match ) ]

type CalcStep
  = ( Justification -- step justification
    , Term )  -- previous term

type Justification
  = ( String   -- law name
    , Binding  -- binding from law variables to goal components
    , [Int] )  -- zipper descent arguments
\end{code}

\begin{code}

-- temporary
dispLiveProof :: LiveProof -> String
dispLiveProof ( nm, _, sc, _, tz, dpath, mtchs, steps )
 = unlines'
     ( ( ("Proof for '"++red nm++"'  "++trSideCond sc)
       : " ..."
       : map shLiveStep (reverse steps)
       )
       ++
       ( displayMatches mtchs
         : [ underline "           "
           , dispSeqZip tz
           , "" ]
       ) )

dispSeqZip :: SeqZip -> String
dispSeqZip (tz,Sequent' _ sc conj')  =  unlines' $ dispConjParts tz sc conj'

dispConjParts tz sc (CLaws' hthry Lft rightC)
  =     [ "R-target = "++trTerm 0 rightC++"  "++trSideCond sc]
     ++ (dispHypotheses hthry)
        : [ _vdash ]
     ++ [trTermZip tz]

dispConjParts tz sc (CLaws' hthry Rght leftC)
  =     [ "L-target = "++trTerm 0 leftC++"  "++trSideCond sc]
     ++ (dispHypotheses hthry)
        : [ _vdash ]
     ++ [trTermZip tz]

dispConjParts tz sc _
 = [trTermZip tz ++ "  "++trSideCond sc++" (Hypotheses not shown)"]

dispHypotheses hthry  =  showLaws $ laws $ hthry

dispTermZip :: TermZip -> String
dispTermZip tz = blue $ trTerm 0 (getTZ tz)

shLiveStep :: CalcStep -> String
shLiveStep ( (lnm, bind, dpath), t )
 = unlines' [ trTerm 0 t
            , "   = '"++lnm++"@" ++ show dpath ++ "'"
            ]

displayMatches :: Matches -> String
displayMatches []  =  ""
displayMatches matches  =  unlines' ( ("Matches:") : map shMatch matches)

shMatch (i, (n, (lt,lsc), bind, rt))
 = ( show i ++ " : "++ ldq ++ green n ++ rdq
     ++ " gives     "
     ++ (bold . blue)
           ( trTerm 0 (fromJust $ instantiate bind rt)
             ++ "  "
             ++ trSideCond (fromJust $ instantiateSC bind lsc) ) )
\end{code}

We then continue with a proof (record):
\begin{code}
type Proof
  = ( String -- assertion name
    , Assertion
    , Calculation -- Simple calculational proofs for now
    )

type Calculation
  = ( Term -- end (or current) term
    , [ CalcStep ] )  -- calculation steps, in proof order


displayProof :: Proof -> String
displayProof (pnm,(trm,sc),(trm',steps))
 = unlines' ( (pnm ++ " : " ++ trTerm 0 trm ++ " " ++ trSideCond sc)
              : "---"
              : ( map shStep steps )
              ++ [trTerm 0 trm'] )

shStep :: CalcStep -> String
shStep ( (lnm, bind, dpath), t )
 = unlines' [ trTermZip $ pathTZ (tail dpath) t -- ignore sequent no at start
                                                -- for now
            , " = '"++lnm++" @" ++ show dpath ++ "'"
            , trBinding bind
            ]
\end{code}

We need to setup a proof from a conjecture:
\begin{code}
startProof :: TheLogic -> [Theory] -> String -> Assertion -> LiveProof
startProof logic thys nm asn@(t,sc)
  = (nm, asn, sc, mcs, sz, atCleft, [], [])
  where
    sz = leftConjFocus $ fromJust $ reduce logic thys (nm,asn)
    mcs = buildMatchContext thys

launchProof :: [Theory] -> String -> Assertion -> Sequent -> LiveProof
launchProof thys nm asn@(t,sc) seq
  = (nm, asn, sc, mcs, sz, atCleft, [], [])
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
proofComplete logic (_, _, _, _, sz, _, _, _)
  =  let sequent = exitSeqZipper sz
     in cleft sequent == cright sequent -- should be alpha-equivalent
\end{code}

We need to convert a complete live proof to a proof:
\begin{code}
finaliseProof :: LiveProof -> Proof
finaliseProof (nm, asn, _, _, (tz,_), _, _, steps)
  = (nm, asn, (exitTZ tz, reverse steps))
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
matchInContexts logic [] t = []
matchInContexts logic ((lws,vts):mcs') t
  = matchLaws logic vts t lws ++ matchInContexts logic mcs' t
\end{code}

Now, the code to match laws, given a context.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: TheLogic -> [VarTable] -> Term -> [(String,Assertion)] -> Matches
matchLaws logic vts t laws
  = zip [1..] (concat $ map (domatch logic vts t) laws)
\end{code}

For each law,
we check its top-level to see if it is an instance of \texttt{theEqv},
in which case we try matches against all possible variations.
\begin{code}
domatch logic vts tC (n,asn@(tP@(Cons tk i ts@(_:_:_)),sc))
  | i == theEqv logic  =  concat $ map (eqvMatch vts tC) $ listsplit ts
  where
      -- tC :: equiv(tsP), with replacement equiv(tsR).
    eqvMatch vts tC (tsP,tsR)
      = justMatch (eqv tsR) vts tC (n,(eqv tsP,sc))
    eqv []   =  theTrue logic
    eqv [t]  =  t
    eqv ts   =  Cons tk i ts
\end{code}

Otherwise we just match against the whole law.
\begin{code}
domatch logic vts tC law
 = justMatch (theTrue logic) vts tC law

justMatch repl vts tC (n,asn@(tP,_))
 = case match vts tC tP of
     Nothing -> []
     Just bind -> [(n,asn,bind,repl)]
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
  =  unlines $ map (numberItem showItem) $  zip [1..] list
numberItem showItem (i,item)
  =  pad 4 istr ++ istr ++ ". " ++ showItem item
  where istr = show i

pad w str
  | ext > 0    =  replicate ext ' '
  | otherwise  =  ""
  where ext = w - length str
\end{code}

Showing theories:
\begin{code}
showTheories [] = "No theories present."
showTheories (thry:_)
  = unlines'
      [ "Theory (top) '"++thName thry++"'"
      , trVarTable (knownV thry)
      , showLaws (laws thry) ]

showLaws lws  =  numberList (showLaw $ nameWidth lws) lws

nameWidth lws = maximum $ map (length . getName) lws
getName (nm,_) = nm
showLaw w (nm,(t,sc))
  =    ldq ++ nm ++ rdq ++ pad w nm
    ++ "  " ++ trTerm 0 t ++ "  "++trSideCond sc
\end{code}

Showing Proof:
\begin{code}
showLivePrf Nothing = "no Proof."
showLivePrf (Just proof) = dispLiveProof proof
\end{code}

Showing Proofs:
\begin{code}
showProofs = unlines' . map ( ('\n':) . displayProof )
\end{code}
