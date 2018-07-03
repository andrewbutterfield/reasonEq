\section{Sequents}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Sequents
 ( Sequent(..)
 , availableStrategies, reduce, redboth, assume
 , Sequent'(..), SeqZip, dispSeqZip
 , leftConjFocus, rightConjFocus, hypConjFocus, exitSeqZipper
 , upSZ, downSZ
 , seqGoLeft, seqGoRight, switchLeftRight
 , seqGoHyp, seqLeaveHyp
 , getHypotheses
 , CalcStep
 , Calculation
 , Proof, displayProof
 , showLogic, showTheories, showNmdAssns, showLaws, showProofs
 , numberList
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
import Proofs
import Theories
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

We define types, inclusing zippers,for sequents.

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
availableStrategies :: TheLogic -> Theories -> NmdAssertion
                    -> [(String,Sequent)]
availableStrategies theLogic theories (nm,(tconj,sc))
  = catMaybes
     [ reduce  theLogic thys cflat
     , redboth theLogic thys cflat
     , assume  theLogic thys cflat ]
  where
    -- these need to be ordered by dependencies !!!!!
    thys = map snd $ M.assocs theories
    cflat = (nm,(flattenTheImp theLogic tconj,sc))
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
  where hthry = Theory { thName = "H."++nm
                       , thDeps = []
                       , laws = []
                       , knownVars = makeUnknownKnown thys t
                       , conjectures = []
                       , proofs = [] }
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
  where hthry = Theory { thName = "H."++nm
                       , thDeps = []
                       , laws = []
                       , knownVars = makeUnknownKnown thys t
                       , conjectures = []
                       , proofs = [] }
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
    hthry = Theory { thName = "H."++nm
                   , thDeps = []
                   , laws = hlaws
                   , knownVars = makeUnknownKnown thys t
                   , conjectures = []
                   , proofs = [] }
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
     vts = map knownVars thys
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
  = do let hthry = hyp sequent
       (before,((hnm,(ht,hsc)),hprov),after) <- peel i $ laws hthry
       return ( mkTZ ht
              , Sequent' (ante sequent)
                         (sc sequent) $
                         HLaws' (thName hthry) (knownVars hthry)
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
  =  ( Theory { thName = hnm
              , thDeps = []
              , laws = ( reverse hbef
                         ++ [((fnm,(horig,fsc)),fprov)]
                         ++ haft
                         ++ [((fnm,(currT,fsc)),fprov)] )
              , knownVars = hkn
              , conjectures = []
              , proofs = [] }
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
  =  Theory { thName = hn
            , thDeps = []
            , laws =  (reverse hbef ++ haft)
            , knownVars = hk
            , conjectures = []
            , proofs = [] }

\end{code}

\begin{code}
-- temporary
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
     hthry = Theory { thName = hn
                    , thDeps = []
                    , laws = (reverse hbef ++ haft)
                    , knownVars = hk
                    , conjectures = []
                    , proofs = [] }

dispHypotheses hthry  =  numberList' showHyp $ laws $ hthry
showHyp ((_,(trm,_)),_) = trTerm 0 trm

dispTermZip :: TermZip -> String
dispTermZip tz = blue $ trTerm 0 (getTZ tz)
\end{code}