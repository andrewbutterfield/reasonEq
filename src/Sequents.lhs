\section{Sequents}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018-22

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Sequents
 ( Sequent(..)
 , TermSC, NamedTermSC
 , availableStrategies
 , reduceAll, reduceBoth, reduceToLeftmost, reduceToRightmost
 , deduce
 , Sequent'(..)
 , SeqZip, writeSeqZip, readSeqZip
 , sequentFocus
 , dispSeqZip, dispSeqTermZip
 , leftConjFocus, rightConjFocus, hypConjFocus, exitSeqZipper
 , upSZ, downSZ
 , switchLeftRight
 , seqGoHyp, seqLeaveHyp
 , getHypotheses
 , zipperVarsMentioned
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
import FreeVars
import SideCond
import Assertions
import TermZipper
import VarData
import Laws
import Proofs
import Theories

import Symbols
import TestRendering

import Debugger
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

Here we unwrap \texttt{Assertion}s.
\begin{code}
type TermSC = (Term, SideCond)
type NamedTermSC = (String, TermSC)
\end{code}


Given any conjecture (named assertion)
we want to determine which strategies apply
and provide a choice of sequents.
We flatten the implication when considering assumption-based sequents
\begin{code}
availableStrategies :: Theories -> String -> NmdAssertion
                    -> [(String,Sequent)]
availableStrategies theories thnm (nm,(Assertion tconj sc))
  = catMaybes
     [ redAll  thys cnj
     , redL2R thys cnj
     , redR2L thys cnj
     , redboth thys cnj
     , deduce  thys cflat ]
  where
    cnj = (nm,(tconj,sc))
    thys = fromJust $ getTheoryDeps thnm theories
    cflat = (nm,(flattenImp tconj, sc))
\end{code}
and then use the following functions to produce a sequent, if possible.

\subsubsection{No Hypotheses}
\begin{code}
noHyps nm = nullTheory{ thName   =  "H."++nm }
\end{code}

\subsubsection{Strategy \textit{redAll}}

\begin{eqnarray*}
   redAll(C)
   &\defs&
   \mathcal L \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
redAll :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
       -> m (String, Sequent)
redAll thys (nm,(t,sc))
  = return ( reduceAll, Sequent thys (noHyps nm) sc t $ theTrue )
reduceAll = "red-All"
\end{code}



\newpage
\subsubsection{Strategy \textit{redboth}}

\begin{eqnarray*}
   redboth(C_1 \equiv C_2)
   &\defs&
   \mathcal L \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
redboth :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
        -> m (String, Sequent)
redboth thys (nm,(t@(Cons tk sb i [tl,tr]),sc))
  | i == theEqv
      = return ( reduceBoth, Sequent thys (noHyps nm) sc tl tr )
redboth thys (nm,(t,sc)) = fail "redboth not applicable"
reduceBoth = "red-bth"
\end{code}

\subsubsection{Strategy \textit{redR2L}}

We will need to convert $\seqof{P_1,\dots,P_n}$, for $n\geq 1$
to $P_1 \equiv \dots \equiv P_n$,
in this, and the next strategy.
\begin{code}
bEqv _ _ [p]  =  p
bEqv sn n ps = Cons P sn n ps
\end{code}


\begin{eqnarray*}
   redR2L(C_1 \equiv C_2 \equiv \dots \equiv C_n)
   &\defs&
   \mathcal L \vdash (C_2 \equiv \dots \equiv C_n) \equiv C_1
\end{eqnarray*}
\begin{code}
redR2L :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
        -> m (String, Sequent)
redR2L thys (nm,(t@(Cons tk si i (c1:cs@(_:_))),sc))
  | i == theEqv
      = return ( reduceToLeftmost,
                 Sequent thys (noHyps nm) sc (bEqv si i cs) c1 )
redR2L thys (nm,(t,sc)) = fail "redR2L not applicable"
reduceToLeftmost = "red-R2L"
\end{code}

\subsubsection{Strategy \textit{redL2R}}

\begin{eqnarray*}
   redL2R(C_1 \equiv \dots \equiv C_{n-1} \equiv C_n)
   &\defs&
   \mathcal L \vdash (C_1 \equiv \dots \equiv C_{n-1}) \equiv C_n
\end{eqnarray*}
We prefer to put the smaller simpler part on the right.
\begin{code}
redL2R :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
        -> m (String, Sequent)
redL2R thys (nm,(t@(Cons tk si i cs@(_:_:_)),sc))
  | i == theEqv
      = return ( reduceToRightmost,
                 Sequent thys (noHyps nm) sc (bEqv si i cs') cn )
  where (cs',cn) = splitLast cs
redL2R thys (nm,(t,sc)) = fail "redL2R not applicable"
reduceToRightmost = "red-L2R"
\end{code}

\newpage
\subsubsection{Strategy \textit{deduce}}

\begin{eqnarray*}
   deduce(H \implies C)
   &\defs&
   \mathcal L,\splitand(H) \vdash (C \equiv \true)
\end{eqnarray*}
\begin{code}
deduce :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
       -> m (String, Sequent)
deduce thys (nm,(t@(Cons tk si i [ta,tc]),sc))
  | i == theImp
    = return ( "deduce", Sequent thys hthry sc tc $ theTrue )
  where
    hlaws = map mkHLaw $ zip [1..] $ splitAnte ta
    mkasn trm = fromJust $ mkAsn trm scTrue -- always succeeds
    mkHLaw (i,trm) = labelAsAxiom ("H."++nm++"."++show i,mkasn trm)
    hthry = nullTheory { 
      thName   =  "H."++nm
    , laws     =  hlaws
    , known    =  makeUnknownKnown thys t
    }
deduce _ _ = fail "deduce not applicable"

splitAnte :: Term -> [Term]
splitAnte (Cons tk si i ts)
 | i == theAnd  =  ts
splitAnte t     =  [t]
\end{code}

\newpage
\subsubsection{Strategy \textit{asmboth}}


\begin{eqnarray*}
   asmboth(H \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\splitand(H) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
asmboth :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
        -> m (String, Sequent)
asmboth thys (nm,(t,sc)) = fail "asmboth not applicable"
\end{code}

\subsubsection{Strategy \textit{shunt}}

\begin{eqnarray*}
   shunt(H_1 \implies \dots H_m \implies C)
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C \equiv \true
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
shunt :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
      -> m (String, Sequent)
shunt thys (nm,(t,sc)) = fail "shunt not applicable"
\end{code}

\subsubsection{Strategy \textit{shntboth}}


\begin{eqnarray*}
   shntboth(H_1 \implies \dots H_m \implies (C_1 \equiv C_2))
   &\defs&
   \mathcal L,\bigcup_{j \in 1\dots m}\splitand(H_j) \vdash C_1 \equiv C_2
\end{eqnarray*}
\begin{code}
-- actually, this is done under the hood
shntboth :: (Monad m, MonadFail m) => [Theory] -> NamedTermSC
        -> m (String, Sequent)
shntboth thys (nm,(t,sc)) = fail "shntboth not applicable"
\end{code}

\subsubsection{Splitting Conjoined Hypotheses}

\begin{eqnarray*}
   \splitand(H_1 \land \dots \land H_n)
   &\defs&
   \setof{H_1,\dots,H_n}
\end{eqnarray*}
\begin{code}
splitAnd :: Term -> [Term]
splitAnd (Cons _ True i ts)
  | i == theAnd  =  ts
splitAnd t       =  [t]
\end{code}


\newpage
\subsection{Making Unknown Variables Known}

A key function is one that makes all unknown variables in a term become known.
\begin{code}
makeUnknownKnown :: [Theory] -> Term -> VarTable
makeUnknownKnown thys t
  = let
     fvars = S.toList $ theFreeVars $ freeVars t
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
            Nothing   ->  error ("Sequents.checkVarStatus FAILED: "++show v)
            Just vt'  ->  vt'
      _               ->  vt

checkLVarStatus :: [VarTable] -> VarTable -> ListVar -> VarTable
checkLVarStatus vts vt lv@(LVbl v _ _)
  = case lookupLVarTables vts v of
      UnknownListVar
       -> case addAbstractVarList v vt of
            Nothing   ->  error ("Sequents.checkLVarStatus FAILED: "++show lv)
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

readSequent' :: (Monad m, MonadFail m) => [Theory] -> [String] -> m (Sequent',[String])
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

readSeqZip :: (Monad m, MonadFail m) => [Theory] -> [String] -> m (SeqZip,[String])
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
hypConjFocus :: (Monad m, MonadFail m) => Int -> Sequent -> m SeqZip
hypConjFocus i sequent
  = do let hthry = hyp sequent
       (before,((hnm,hasn),hprov),after) <- peel i $ laws hthry
       let ht = assnT hasn
       return ( mkTZ ht
              , Sequent' (ante sequent)
                         (sc sequent) $
                         HLaws' (thName hthry) (known hthry)
                                before hnm (assnC hasn) hprov ht after
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
  =  (  nullTheory { 
        thName   =  hnm      , thDeps   =  []
      , laws     =  ( reverse hbef
                    ++ [((fnm,horig'),fprov)]
                    ++ haft
                    ++ [((fnm,currT'),fprov)] )
      , known    =  hkn
      }
     , cl, cr)
  where horig' = fromJust $ mkAsn horig fsc
        currT' = fromJust $ mkAsn currT fsc
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
  = nullTheory { 
      thName   =  hn    , thDeps   =  []
    , laws     =  (reverse hbef ++ haft)
    , known    =  hk
    }

\end{code}


\subsection{Sequent Mentioned Variables}

When generating fresh variables,
we need to know the state of the entire goal conjecture
at the relevant part of the proof,
and not just that of the current focus, or sequent sub-component.
We will have access to all of the above via the top-level zipper:
\begin{code}
zipperVarsMentioned :: SeqZip -> VarSet
zipperVarsMentioned (tz,sequent')
  = mentionedVars (exitTZ tz)
    `S.union`
    seqVarsMentioned sequent'
\end{code}

\begin{code}
seqVarsMentioned :: Sequent' ->  VarSet
seqVarsMentioned sequent'  =  lawsVarsMentioned $ laws' sequent'
\end{code}

\begin{code}
lawsVarsMentioned :: Laws' -> VarSet
lawsVarsMentioned (CLaws' hyp _ other)
  =  (S.unions $ map lawVarsMentioned $ laws hyp)
     `S.union`
     mentionedVars other
lawsVarsMentioned hlaws'@(HLaws' _ _ _ _ _ _ _ _ _ _)
  =  (S.unions $ map lawVarsMentioned $ hbefore hlaws')
     `S.union`
     (S.unions $ map lawVarsMentioned $ hafter hlaws')
     `S.union`
     (mentionedVars $ cleft0 hlaws')
     `S.union`
     (mentionedVars $ cright0 hlaws')
\end{code}

\begin{code}
lawVarsMentioned :: Law -> VarSet
lawVarsMentioned = mentionedVars . assnT . snd . fst
\end{code}

\newpage
\subsection{Showing Sequents}

\textbf{This should all be done via proper generic rendering code}

\begin{code}
-- temporary
dispSeqZip :: [Int] -> SideCond -> SeqZip -> String
dispSeqZip fp sc (tz,Sequent' _ _ conj')
                                     =  unlines' $ dispConjParts fp tz sc conj'

dispConjParts fp tz sc (CLaws' hthry Lft rightC)
  =  (dispHypotheses hthry)
     : [ _vdash ]
     ++ dispGoal tz sc
     ++ dispContext fp "Target (RHS): " (red $ trTerm 0 rightC)


dispConjParts fp tz sc (CLaws' hthry Rght leftC)
  =  (dispHypotheses hthry)
     : [ _vdash ]
     ++ dispGoal tz sc
     ++ dispContext fp "Target (LHS): " (red $ trTerm 0 leftC)


dispConjParts fp tz sc seq'@(HLaws' hn hk hbef _ _ _ horig haft _ _)
  =  (dispHypotheses $ getHypotheses' seq')
     : [ _vdash ]
     ++ dispGoal tz sc
     ++ dispContext fp "Hypothesis: " (trTerm 0 horig++"  "++trSideCond sc)
  where
     hthry =  nullTheory { 
                thName   =  hn
              , laws     =  (reverse hbef ++ haft)
              , known    =  hk
              }


dispHypotheses hthry  =  numberList' showHyp $ laws $ hthry
showHyp ((_,(Assertion trm _)),_) = trTerm 0 trm

dispGoal tz sc
  = [ trTermZip tz++"    "++trSideCond sc ]

dispContext fp what formula
  = [ "Focus = " ++ show fp, ""
    , what
    , formula
    ]

dispSeqTermZip :: SeqZip -> String
dispSeqTermZip (tz,_) = trTermZip tz

dispTermZip :: TermZip -> String
dispTermZip tz = blue $ trTerm 0 (getTZ tz)
\end{code}
