\section{Sequents}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Sequents
 ( Sequent(..)
 , availableStrategies
 , reduce, redboth, redtail, redinit
 , assume
 , Sequent'(..)
 , SeqZip, writeSeqZip, readSeqZip
 , sequentFocus
 , dispSeqZip, dispSeqTermZip
 , leftConjFocus, rightConjFocus, hypConjFocus, exitSeqZipper
 , upSZ, downSZ
 , switchLeftRight
 , seqGoHyp, seqLeaveHyp
 , getHypotheses
 , CalcStep
 , Calculation
 , Proof, displayProof
 , showLogic, showTheories, showNmdAssns, showLaws
 , numberList
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import Utilities
import WriteRead
import Variables
import AST
import SideCond
import TermZipper
import VarData
import Laws
import Proofs
import Theories

import NiceSymbols
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types, including zippers,for sequents.

\newpage
\subsection{Sequent Type}

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

\subsection{Sequent Strategies}

Given any conjecture (named assertion)
we want to determine which strategies apply
and provide a choice of sequents.
We first flatten the implication (if any),
\begin{code}
availableStrategies :: LogicSig -> Theories -> String -> NmdAssertion
                    -> [(String,Sequent)]
availableStrategies theSig theories thnm (nm,(tconj,sc))
  = catMaybes
     [ reduce  theSig thys cflat
     , redboth theSig thys cflat
     , redtail theSig thys cflat
     , redinit theSig thys cflat
     , assume  theSig thys cflat ]
  where
    thys = fromJust $ getTheoryDeps thnm theories
    cflat = (nm,(flattenTheImp theSig tconj,sc))
\end{code}
and then use the following functions to produce a sequent, if possible.

\subsubsection{No Hypotheses}
\begin{code}
noHyps nm = Theory { thName = "H."++nm
                   , thDeps = []
                   , known = newVarTable
                   , laws = []
                   , proofs = []
                   , conjs = []
                   }
\end{code}

\subsubsection{Strategy \textit{reduce}}

\begin{eqnarray*}
   reduce(C)
   &\defs&
   \mathcal L \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
reduce :: Monad m => LogicSig -> [Theory] -> NmdAssertion
       -> m (String, Sequent)
reduce logicsig thys (nm,(t,sc))
  = return ( "reduce", Sequent thys (noHyps nm) sc t $ theTrue logicsig )
\end{code}



\newpage
\subsubsection{Strategy \textit{redboth}}

We will need to convert $\seqof{P_1,\dots,\P_n}$, for $n\geq 1$
to $P_1 \equiv \dots \equiv P_n$.
\begin{code}
bEqv n [p]  =  p
bEqv n ps = Cons P n ps
\end{code}

\begin{eqnarray*}
   redboth(C_1 \equiv C_2)
   &\defs&
   \mathcal L \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
redboth :: Monad m => LogicSig -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
redboth logicsig thys (nm,(t@(Cons tk i [tl,tr]),sc))
  | i == theEqv logicsig
      = return ( "redboth", Sequent thys (noHyps nm) sc tl tr )
redboth logicsig thys (nm,(t,sc)) = fail "redboth not applicable"
\end{code}

\subsubsection{Strategy \textit{redtail}}

\begin{eqnarray*}
   redtail(C_1 \equiv C_2 \equiv \dots \equiv C_n)
   &\defs&
   \mathcal L \vdash (C_2 \equiv \dots \equiv C_n) \equiv C_1
\end{eqnarray*}
\begin{code}
redtail :: Monad m => LogicSig -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
redtail logicsig thys (nm,(t@(Cons tk i (c1:cs@(_:_))),sc))
  | i == theEqv logicsig
      = return ( "redtail", Sequent thys (noHyps nm) sc (bEqv i cs) c1 )
redtail logicsig thys (nm,(t,sc)) = fail "redtail not applicable"
\end{code}

\subsubsection{Strategy \textit{redinit}}

\begin{eqnarray*}
   redinit(C_1 \equiv \dots \equiv C_{n-1} \equiv C_n)
   &\defs&
   \mathcal L \vdash (C_1 \equiv \dots \equiv C_{n-1}) \equiv C_n
\end{eqnarray*}
We prefer to put the smaller simpler part on the right.
\begin{code}
redinit :: Monad m => LogicSig -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
redinit logicsig thys (nm,(t@(Cons tk i cs@(_:_:_)),sc))
  | i == theEqv logicsig
      = return ( "redinit", Sequent thys (noHyps nm) sc (bEqv i cs') cn )
  where (cs',cn) = splitLast cs
redinit logicsig thys (nm,(t,sc)) = fail "redinit not applicable"
\end{code}

\newpage
\subsubsection{Strategy \textit{assume}}

\begin{eqnarray*}
   assume(H \implies C)
   &\defs&
   \mathcal L,\splitand(H) \vdash (C \equiv \true)
\end{eqnarray*}
\begin{code}
assume :: Monad m => LogicSig -> [Theory] -> NmdAssertion
       -> m (String, Sequent)
assume logicsig thys (nm,(t@(Cons tk i [ta,tc]),sc))
  | i == theImp logicsig
    = return ( "assume", Sequent thys hthry sc tc $ theTrue logicsig )
  where
    hlaws = map mkHLaw $ zip [1..] $ splitAnte logicsig ta
    mkHLaw (i,trm) = labelAsAxiom ("H."++nm++"."++show i,(trm,scTrue))
    hthry = Theory { thName = "H."++nm
                   , thDeps = []
                   , laws = hlaws
                   , known = makeUnknownKnown thys t
                   , proofs = []
                   , conjs = []
                   }
assume _ _ _ = fail "assume not applicable"

splitAnte :: LogicSig -> Term -> [Term]
splitAnte theSig (Cons tk i ts)
 | i == theAnd theSig  =  ts
splitAnte _        t     =  [t]
\end{code}

\newpage
\subsubsection{Strategy \textit{asmboth}}


\begin{eqnarray*}
   asmboth(H \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\splitand(H) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
asmboth :: Monad m => LogicSig -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
asmboth logicsig thys (nm,(t,sc)) = fail "asmboth not applicable"
\end{code}

\subsubsection{Strategy \textit{shunt}}

\begin{eqnarray*}
   shunt(H_1 \implies \dots H_m \implies C)
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
shunt :: Monad m => LogicSig -> [Theory] -> NmdAssertion
      -> m (String, Sequent)
shunt logicsig thys (nm,(t,sc)) = fail "shunt not applicable"
\end{code}

\subsubsection{Strategy \textit{shntboth}}


\begin{eqnarray*}
   shntboth(H_1 \implies \dots H_m \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
shntboth :: Monad m => LogicSig -> [Theory] -> NmdAssertion
        -> m (String, Sequent)
shntboth logicsig thys (nm,(t,sc)) = fail "shntboth not applicable"
\end{code}

\subsubsection{Splitting Conjoined Hypotheses}

\begin{eqnarray*}
   \splitand(H_1 \land \dots \land H_n)
   &\defs&
   \setof{H_1,\dots,H_n}
\end{eqnarray*}
\begin{code}
splitAnd :: LogicSig -> Term -> [Term]
splitAnd logicsig (Cons _ i ts)
  | i == theAnd logicsig  =  ts
splitAnd _ t           =  [t]
\end{code}


\newpage
\subsection{Making Unknown Variables Known}

A key function is one that makes all unknown variables in a term become known.
\begin{code}
makeUnknownKnown :: [Theory] -> Term -> VarTable
makeUnknownKnown thys t
  = let
     fvars = S.toList $ freeVars t
     vts = map known thys
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

We will need a zipper for sequents as we can focus in on any term
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
   T^* \times SC \times N \times VD  \times L^* \times N
       \times SC \times P \times L^* \times t^2
\\&=&\textrm{Fold instance of  $T$}
\\&& T^* \times SC \times T \times \mathbf{2} \times t
   \quad+\quad
   T^* \times SC \times N \times VD  \times L^* \times N
       \times SC \times P \times L^* \times t^2
\\&=&\textrm{Common factor}
\\&& T^* \times SC \times
   \left(\quad
          T \times \mathbf{2} \times t
          \quad+\quad
          N \times VD \times L^* \times N
            \times SC \times P   \times L^* \times t^2
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

Writing and Reading Sequent derivatives.
\begin{code}
sequent' = "SEQUENT'"
seq'HDR = "BEGIN "++sequent' ; seq'TRL = "END "++sequent'
sc0KEY = "SIDECOND = "
laws'KEY = "LAWS' = "

writeSequent' :: Sequent' -> [String]
writeSequent' seq'
  = [ seq'HDR
    -- we don't save theories here
    , sc0KEY ++ show (sc0 seq')
    , laws'KEY ++ show (laws' seq')
    , seq'TRL ]

readSequent' :: Monad m => [Theory] -> [String] -> m (Sequent',[String])
readSequent' thylist txts
  = do rest1 <- readThis seq'HDR txts
       -- theories are supplied, reconstructed in REqState read.
       (sc,rest2) <- readKey sc0KEY read rest1
       (lw',rest3) <- readKey laws'KEY read rest2
       rest4 <- readThis seq'TRL rest3
       return ( Sequent' {
                  ante0 = thylist
                , sc0 = sc
                , laws' = lw'
                }
              , rest4 )
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

seqzip = "SEQZIP"
szHDR = "BEGIN "++seqzip ; szTRL = "END " ++ seqzip

tzKEY = "TERMZIP = "
seq'KEY = "SEQUENT' = "

writeSeqZip :: SeqZip -> [String]
writeSeqZip (tz,seq')
  = [ szHDR
    , tzKEY ++ show tz ] ++
    writeSequent' seq' ++
    [ szTRL ]

readSeqZip :: Monad m => [Theory] -> [String] -> m (SeqZip,[String])
readSeqZip thylist txts
  = do rest1 <- readThis szHDR txts
       (tz,rest2) <- readKey tzKEY read rest1
       (seq',rest3) <- readSequent' thylist rest2
       rest4 <- readThis szTRL rest3
       return ((tz,seq'),rest4)
\end{code}

It is useful to be able to determine where we are currently
focussed at sequent level:
\begin{code}
sequentFocus :: SeqZip -> SeqFocus
sequentFocus (_,seq')
 = case laws' seq' of
     (CLaws' _ which _) | which == Lft   ->  CLeft
                        | which == Rght  ->  CRight
     (HLaws' _ _ before _ _ _ _ _ _ _)   ->  Hyp (length before + 1)
\end{code}

\newpage
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
                         HLaws' (thName hthry) (known hthry)
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
              , known = hkn
              , conjs = []
              , proofs = []
              }
     , cl, cr)
\end{code}

\newpage
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
switchLeftRight :: SeqZip -> (Bool, Justification, SeqZip)
switchLeftRight sz@(_,Sequent' _ _ (CLaws' _ Lft _)) -- already Left
  =  (True, Switch CLeft CRight, rightConjFocus $ exitSeqZipper sz)
switchLeftRight sz@(_,Sequent' _ _ (CLaws' _ Rght _)) -- already Right
  =  (True, Switch CRight CLeft,  leftConjFocus $ exitSeqZipper sz)
switchLeftRight sz -- must be in hypothesis
  =  (False, error "switchLeftRight: in hypothesis!", sz)
\end{code}

Entering a $H_i$  from $C_{left}$ or $C_{right}$ is easy.
But once in, we need a special command to exit.
\begin{code}
seqGoHyp :: Int -> SeqZip -> (Bool, Justification, SeqZip)
seqGoHyp i sz@(_,Sequent' _ _ (HLaws' _ _ _ _ _ _ _ _ _ _))
  =  (False, undefined, sz)  -- can't change hypothesis while in one.
seqGoHyp i sz
  =  case hypConjFocus i $ exitSeqZipper sz of
       Nothing   ->  (False,error ("seqGoHyp: bad index "++show i),sz)
       Just sz'  ->  (True,Switch (sequentFocus sz) (Hyp i), sz')
\end{code}

When we leave, the revised hypothesis must be added in as a new one.
\begin{code}
seqLeaveHyp :: SeqZip -> (Bool, Justification, SeqZip)
seqLeaveHyp sz@(_,Sequent' _ _ (HLaws' _ _ _ _ _ _ _ _ _ _))
  =  (True,Switch (sequentFocus sz ) CLeft, leftConjFocus $ exitSeqZipper sz)
seqLeaveHyp sz -- not in hypothesis
  =  (False,error "seqLeaveHyp: not in hyp.",sz)
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
            , known = hk
            , conjs = []
            , proofs = [] }

\end{code}

\newpage
\subsection{Showing Sequents}

\textbf{This should all be done via proper generic rendering code}

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
                    , known = hk
                    , conjs = []
                    , proofs = []
                    }

dispHypotheses hthry  =  numberList' showHyp $ laws $ hthry
showHyp ((_,(trm,_)),_) = trTerm 0 trm

dispSeqTermZip :: SeqZip -> String
dispSeqTermZip (tz,_) = trTermZip tz

dispTermZip :: TermZip -> String
dispTermZip tz = blue $ trTerm 0 (getTZ tz)
\end{code}
