\section{Side Conditions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SideCond ( VarSideCond, pattern Exact, pattern Approx
           , pattern Disjoint, pattern Covers, pattern DisjCov, pattern PreDisj
           , vscTrue
           , addPreSC, addExactSC, addDisjSC, addCoverSC, checkNewSC
           , VarSCMap, SideCond, scTrue
           , pattern SC, pattern Fresh, pattern VarSCs, sidecond
           , mrgSideCond
           , notin, is, covers, fresh, pre
           , int_tst_SideCond
           ) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import LexBase
import Variables

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}


\subsection{Introduction}

A side-condition is a property used in laws,
typically putting a constraint on the free variables of some term.
In many logics, these can be checked by simple inspection of a term.
However,
given a logic like ours with explict expression and predicate
(a.k.a. \emph{schematic}) variables this is not always possible.

A side condition is about a relationship between the free variables
of term ($T$),
and a set of other (general) variables ($x,\lst{v}$)
The relationship can have the form:
\begin{eqnarray*}
   x,\lst v   \notin  \fv(T) && \mbox{disjoint}
\\ x,\lst v      =    \fv(T) && \mbox{exact}
\\ x,\lst v \supseteq \fv(T) && \mbox{covering}
\\ pre      \supseteq \fv(T) && \mbox{pre-condition}
\end{eqnarray*}

We shall first look at how we internally represent side-conditions.
Later we will describe user-friendly ways to build them.

\subsection{Representing Sideconditions}


Let $D$, $X$ and $C$ denote sets of variables
that are meant to be be disjoint, exact, and covering respectively.
Let $pre$ denote the assertion that the term has only pre-variables.
Let $F$ denote the free variables of the expression or predicate variable
under consideration.

In addition we may also have a requirement
that certain variables are new, or fresh.
This applies to the whole term being matched,
and not just those terms signified by expression and predicate variables.
Let $N$ denote this set.

Here we use $D$, $X$, $C$, $N$, to represent themselves
and also be a shorthand for $D \cap F = \emptyset$,
$X = F$, $F \subseteq C$,
and $fresh(N)$ respectively.
Which is which should be clear from context.

There are a number of laws that govern how
different combinations of the above side-conditions interact.
\begin{eqnarray*}
   N_1 \land N_2 &=& N_1 \cup N_2
\\ D_1 \land D_2 &=& D_1 \cup D_2
\\ X_1 \land X_2 &=& X_1 = X_2 \;\land\; X_1
\\ C_1 \land C_2 &=& C_1 \cap C_2
\\
\\ N_1 \land X_2 &=& N_1 \cap X_2 = \emptyset \;\land\; N_1 \;\land\; X_1
\\ N_1 \land C_2 &=& N_1 \cap C_1 = \emptyset \;\land\; N_1 \;\land\; C_1
\\ D_1 \land X_2 &=& D_1 \cap X_2 = \emptyset \;\land\; X_2
\\ D_1 \land C_2 &=& C_2 \cap D_1 = \emptyset \;\land\; D_1 \;\land\; C_2
\\ X_1 \land C_2 &=& X_1 \subseteq C_2 \;\land\; X_1
\end{eqnarray*}
Given that variable matching will respect variable roles (\verb"VarWhen"),
if we have either $C$ or $X$ specified,
then we check $pre$ at side-condition generation time.
We can summarise by saying,
given a satisfiable side-condition involving $N$, $D$, $X$, and $C$,
then there is a faithful representation
where the following invariant holds:
\[
N \not\!\cap\; X
\land
N \not\!\cap\; C
\land
D \not\!\cap\; X
\land
D \not\!\cap\; C
\land
X \subseteq C
\]
In fact we see that our representation either consists solely of $X$,
or else contains one or more of $pre$, $D$, or $C$.
If both $pre$ and $C$ were specified,
then we will have checked that all relevant variables in $C$ satisfy $pre$,
and hence it becomes superfluous.

\newpage
\subsubsection{Variable side-conditions}
So, a side-condition associated with a term variable is either exact (\texttt{X}),
or approximate (\texttt{A}):
\begin{code}
data VarSideCond
 = X VarSet
 | A Bool -- true if term must be a pre-condition
     (Maybe VarSet) -- D
     (Maybe VarSet) -- C
 deriving (Eq,Ord,Show,Read)

pattern Exact vs = X vs
pattern Approx pre mD mC <- A pre mD mC
pattern Disjoint d <- A _ (Just d) _
pattern Covers c <- A _ _ (Just c)
pattern DisjCov d c <- A _ (Just d) (Just c)
pattern PreDisj pre d <- A pre (Just d) _
\end{code}

Typically a variable side-condition will be built
from fragments that specify one of $pre$, $D$, $X$ or $C$,
starting with a condition where all parts are ``null'',
signalling a trivially true side-condition.
\begin{code}
vscTrue :: VarSideCond
vscTrue = A False Nothing Nothing
\end{code}

We will want to merge a set with a maybe-set below:
\begin{code}
mrgSet  :: Ord a
          => (Set a -> Set a -> Set a) -> Set a -> Maybe (Set a)
          -> Set a
mrgSet op s Nothing    =  s
mrgSet op s (Just s')  =  s `op` s'

jmrgSet op s ms = Just $ mrgSet op s ms
\end{code}

Variable Side-Condition test values:
\begin{code}
i_a = fromJust $ ident "a"
i_b = fromJust $ ident "b"
i_e = fromJust $ ident "e"
i_f = fromJust $ ident "f"

v_a =  PreVar    $ i_a
v_b =  PreVar    $ i_b
v_a' = PostVar   $ i_a
v_b' = PostVar   $ i_b

gv_a =  StdVar v_a
gv_b =  StdVar v_b
gv_a' = StdVar v_a'
gv_b' = StdVar v_b'

s0   = S.fromList [] :: VarSet
sa   = S.fromList [gv_a]
sa'  = S.fromList [gv_a']
sb   = S.fromList [gv_b]
sab  = S.fromList [gv_a,gv_b]
saa' = S.fromList [gv_a,gv_a']
sab' = S.fromList [gv_a,gv_b']
sbb' = S.fromList [gv_b,gv_b']

sc_pre          =  A True Nothing Nothing
sc_exact_a      =  Exact sa
sc_exact_b      =  Exact sb
sc_exact_ab     =  Exact sab
sc_exact_ab'    =  Exact sab'
sc_cover_a      =  A False Nothing $ Just sa
sc_cover_ab     =  A False Nothing $ Just sab
sc_cover_ab'    =  A False Nothing $ Just sab'
sc_disjoint_a   =  A False (Just sa) Nothing
sc_disjoint_b   =  A False (Just sb) Nothing
sc_disjoint_ab  =  A False (Just sab) Nothing
sc_D_a_C_b      =  A False (Just sa) (Just sb)
sc_D_a_C_bb'    =  A False (Just sa) (Just sbb')
\end{code}

\newpage
\paragraph{Adding $pre$:} check against any pre-existing $X$ or $C$
\begin{code}
addPreSC :: Monad m => VarSideCond -> m VarSideCond

addPreSC vsc@(Exact x)
 | isPreVarSet x   =  return vsc
 | otherwise       =  fail "SideCond.addPreSC: exact set is not a precondition"

addPreSC vsc@(Covers vs)
 | isPreVarSet vs   =  return vsc
 | otherwise        =  fail "SideCond.addPreSC: covering set is not a precondition"

addPreSC (Approx _ mD mC) = return $ A True mD mC
\end{code}

Tests:
\begin{code}
test_add_pre_to_true = testCase "Add pre to trivial SC"
 ( addPreSC vscTrue  @?=  Just sc_pre )

test_add_pre_to_exact_ok = testCase "Add pre to exact SC (OK)"
 ( addPreSC sc_exact_ab  @?=  Just sc_exact_ab )

test_add_pre_to_exact_fail = testCase "Add pre to exact SC (Fail)"
 ( addPreSC sc_exact_ab'  @?=  Nothing )

test_add_pre_to_cover_ok = testCase "Add pre to cover SC (OK)"
 ( addPreSC sc_cover_ab  @?=  Just sc_cover_ab )

test_add_pre_to_cover_fail = testCase "Add pre to cover SC (Fail)"
 ( addPreSC sc_cover_ab'  @?=  Nothing )

test_add_pre_to_disjoint = testCase "Add pre to disjoint"
 ( addPreSC sc_disjoint_ab  @?=  Just (A True (Just sab) Nothing) )

addPreTests = testGroup "SideCond.addPreSC"
               [ test_add_pre_to_true
               , test_add_pre_to_exact_ok
               , test_add_pre_to_exact_fail
               , test_add_pre_to_cover_ok
               , test_add_pre_to_cover_fail
               , test_add_pre_to_disjoint
               ]
\end{code}

\newpage
\paragraph{Adding $D$:} check against any pre-existing $X$ or $C$
\begin{code}
addDisjSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond

addDisjSC d vsc@(Exact x)
 | d `disjoint` x  =  return vsc
 | otherwise       =  fail "SideCond.addDisjSC: exact and disjoint sets overlap"

addDisjSC d (Approx pre mD mC@(Just c))
 | c `disjoint` d  =  return $ A pre (jmrgSet S.union d mD) mC
 | otherwise       =  fail "SideCond.addDisjSC: covering and disjoint sets overlap"

addDisjSC d (Approx pre mD mC)
  = return $ A pre (jmrgSet S.union d mD) mC
\end{code}

Tests:
\begin{code}
test_add_disj_to_true = testCase "Add disjoint to trivial SC"
 ( addDisjSC sab vscTrue  @?=  Just sc_disjoint_ab)

test_add_disj_to_exact_ok = testCase "Add disjoint to exact (Ok)"
 ( addDisjSC sb sc_exact_a  @?=  Just sc_exact_a )

test_add_disj_to_exact_fail = testCase "Add disjoint to exact (Fail)"
 ( addDisjSC sb sc_exact_ab  @?=  Nothing )

test_add_disj_to_cover_ok = testCase "Add disjoint to cover (Ok)"
 ( addDisjSC sb sc_cover_a  @?=  Just (A False (Just sb) (Just sa)) )

test_add_disj_to_cover_fail = testCase "Add disjoint to cover (Fail)"
 ( addDisjSC sb sc_cover_ab  @?=  Nothing )

test_add_disj_to_disj = testCase "Add disjoint to disjoint"
 ( addDisjSC sa sc_disjoint_b  @?=  Just sc_disjoint_ab )

test_add_disj_to_mixed = testCase "Add disjoint to disjoint and cover"
 ( addDisjSC sa' sc_D_a_C_b  @?=  Just (A False (Just saa') (Just sb)) )

addDisjTests = testGroup "SideCond.addDisjSC"
               [ test_add_disj_to_true
               , test_add_disj_to_exact_ok
               , test_add_disj_to_exact_fail
               , test_add_disj_to_cover_ok
               , test_add_disj_to_cover_fail
               , test_add_disj_to_disj
               , test_add_disj_to_mixed
               ]
\end{code}

\newpage
\paragraph{Adding $X$:} check against any pre-existing $pre$, $D$, $X$ or $C$
\begin{code}
addExactSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond

addExactSC x vsc@(Exact x0)
 | x == x0    =  return vsc
 | otherwise  =  fail "SideCond.addExactSC: differing exact sets"

addExactSC x (Approx pre _ _)
 | pre && not (isPreVarSet x) = fail "SideCond.addExactSC: exact set not pre-condition"

addExactSC x (Disjoint d)
 | x `overlaps` d = fail "SideCond.addExactSC: exact and disjoint sets overlap"

addExactSC x (Covers c)
 | not(x `S.isSubsetOf` c) = fail "SideCond.addExactSC: exact not inside covering set"

addExactSC x _ = return $ Exact x
\end{code}

Tests:
\begin{code}
test_add_exact_to_true = testCase "Add exact to trivial SC"
 ( addExactSC sab vscTrue  @?=  Just sc_exact_ab)

test_add_exact_to_exact_ok = testCase "Add exact to exact (Ok)"
 ( addExactSC sa sc_exact_a  @?=  Just sc_exact_a )

test_add_exact_to_exact_fail = testCase "Add exact to exact (Fail)"
 ( addExactSC sb sc_exact_ab  @?=  Nothing )

test_add_exact_to_cover_ok = testCase "Add exact to cover (Ok)"
 ( addExactSC sa sc_cover_ab  @?=  Just sc_exact_a )

test_add_exact_to_cover_fail = testCase "Add exact to cover (Fail)"
 ( addExactSC sb sc_cover_a  @?=  Nothing )

test_add_exact_to_disj = testCase "Add exact to disjoint"
 ( addExactSC sa sc_disjoint_b  @?=  Just sc_exact_a )

test_add_exact_to_mixed = testCase "Add exact to disjoint and cover"
 ( addExactSC sb sc_D_a_C_b  @?=  Just sc_exact_b )

addExactTests = testGroup "SideCond.addExactSC"
               [ test_add_exact_to_true
               , test_add_exact_to_exact_ok
               , test_add_exact_to_exact_fail
               , test_add_exact_to_cover_ok
               , test_add_exact_to_cover_fail
               , test_add_exact_to_disj
               , test_add_exact_to_mixed
               ]
\end{code}

\newpage
\paragraph{Adding $C$:} check against any pre-existing $pre$, $D$, or $X$
\begin{code}
addCoverSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond

addCoverSC c vsc@(Exact x)
 | x `S.isSubsetOf` c  =  return vsc
 | otherwise           =  fail "SideCond.addCoverSC: exact set not inside covering set"

addCoverSC c (Approx pre _ _)
 | pre && not (isPreVarSet c) = fail "SideCond.addCoverSC: cover set not pre-condition"

addCoverSC c (Disjoint d)
 | c `overlaps` d = fail "SideCond.addCoverSC: cover and disjoint sets overlap"

addCoverSC c (Approx pre mD mC)
 | S.null c'  =  return $ Exact S.empty
 | otherwise  =  return $ A pre mD $ Just c'
 where c' = mrgSet S.intersection c mC
\end{code}

Tests:
\begin{code}
test_add_cover_to_true = testCase "Add cover to trivial SC"
 ( addCoverSC sab vscTrue  @?=  Just sc_cover_ab)

test_add_cover_to_exact_ok = testCase "Add cover to exact (Ok)"
 ( addCoverSC sab sc_exact_a  @?=  Just sc_exact_a )

test_add_cover_to_exact_fail = testCase "Add cover to exact (Fail)"
 ( addCoverSC sb sc_exact_ab  @?=  Nothing )

test_add_cover_to_cover_c = testCase "Add cover to cover (still cover)"
 ( addCoverSC sa sc_cover_ab  @?=  Just sc_cover_a )

test_add_cover_to_cover_x = testCase "Add cover to cover (exact)"
 ( addCoverSC sb sc_cover_a  @?=  Just (Exact s0) )

test_add_cover_to_disj = testCase "Add cover to disjoint"
 ( addCoverSC sb sc_disjoint_a  @?=  Just sc_D_a_C_b )

test_add_cover_to_mixed = testCase "Add cover to disjoint and cover"
 ( addCoverSC sb sc_D_a_C_bb'  @?=  Just sc_D_a_C_b )

addCoverTests = testGroup "SideCond.addCoverSC"
               [ test_add_cover_to_true
               , test_add_cover_to_exact_ok
               , test_add_cover_to_exact_fail
               , test_add_cover_to_cover_c
               , test_add_cover_to_cover_x
               , test_add_cover_to_disj
               , test_add_cover_to_mixed
               ]
\end{code}

\subsubsection{Variable condition-add tests}
\begin{code}
varSCTests = testGroup "Adding Variable Side-Conditions"
                [ addPreTests
                , addDisjTests
                , addExactTests
                , addCoverTests
                ]
\end{code}

\subsubsection{Merging Variable Conditions}

\begin{code}
mrgVarSideCond :: Monad m => VarSideCond -> VarSideCond -> m VarSideCond
mrgVarSideCond (X vs) vsc = addExactSC vs vsc
mrgVarSideCond (A pre mD mC) vsc
 = do vsc1 <- mrgD mD vsc
      vsc2 <- mrgC mC vsc1
      if pre then addPreSC vsc2 else return vsc2
 where
   mrgD Nothing vsc   =  return vsc
   mrgD (Just d) vsc  =  addDisjSC d vsc
   mrgC Nothing vsc   =  return vsc
   mrgC (Just c) vsc  =  addCoverSC c vsc
\end{code}


\subsubsection{Full Side Conditions}

Checking $N$ against a variable-side condition, looking at $X$ and $C$.
\begin{code}
checkNewSC :: VarSet -> VarSideCond -> Bool
checkNewSC n (Exact x)   =  n `disjoint` x
checkNewSC n (Covers c)  =  n `disjoint` c
checkNewSC _ _           =  True
\end{code}

A side-condition for a law lumps together $N$
with a mapping from term variables to variable side-conditions.
\begin{code}
type VarSCMap = Map Variable VarSideCond
data SideCond
 = SC VarSet VarSCMap
 deriving (Eq,Ord,Show,Read)
\end{code}
If both entities are empty, then we have the trivial side-condition,
which is always true:
\begin{code}
scTrue :: SideCond
scTrue = SC S.empty M.empty
\end{code}

Test values:
\begin{code}
v_e  = PreExpr  $ i_e
v_f  = PreExpr  $ i_f
v_e' = PostExpr $ i_e
v_f' = PostExpr $ i_f

m_e_pre = M.fromList [(v_e,sc_pre)]
m_e_exact_a = M.fromList [(v_e,sc_exact_a)]
m_e_cover_a = M.fromList [(v_e,sc_cover_a)]
m_e_disjoint_ab = M.fromList [(v_e,sc_disjoint_ab)]
m_e_X_b_f_C_ab = M.fromList [(v_e,sc_exact_b),(v_f,sc_cover_ab)]
\end{code}

Pattern synonyms and builder
\begin{code}
pattern SideCond n vmap <- SC n vmap
pattern Fresh n <- SC n _
pattern VarSCs vmap <- SC _ vmap

sidecond :: Monad m => VarSet -> VarSCMap -> m SideCond
sidecond n vmap
 | all (checkNewSC n) $ M.elems vmap  =  return $ SC n vmap
 | otherwise  =  fail "fresh set conflicts with variable side-condition"
\end{code}

Tests:
\begin{code}
test_sidecond_empty = testCase "Trivial side-condition"
 ( sidecond S.empty M.empty @?=  Just scTrue)

test_sidecond_freshonly = testCase "Only Freshness"
 ( sidecond sab M.empty @?=  Just (SC sab M.empty) )

test_sidecond_one_pre = testCase "One Precondition"
 ( sidecond S.empty m_e_pre @?=  Just (SC S.empty m_e_pre) )

test_sidecond_fresh_exact_ok = testCase "Freshness and Exact (Ok)"
 ( sidecond sb m_e_exact_a @?=  Just (SC sb m_e_exact_a) )

test_sidecond_fresh_exact_fail = testCase "Freshness and Exact (Fail)"
 ( sidecond sa m_e_exact_a @?=  Nothing )

test_sidecond_fresh_cover_ok = testCase "Freshness and Cover (Ok)"
 ( sidecond sb m_e_cover_a @?=  Just (SC sb m_e_cover_a) )

test_sidecond_fresh_cover_fail = testCase "Freshness and Cover (Fail)"
 ( sidecond sa m_e_cover_a @?=  Nothing )

test_sidecond_fresh_exact_cover_fail = testCase "Freshness, Exact and Cover (Fail)"
 ( sidecond sa m_e_X_b_f_C_ab @?=  Nothing )

test_sidecond_fresh_disjoint = testCase "Freshness and Disjoint"
 ( sidecond saa' m_e_disjoint_ab @?=  Just (SC saa' m_e_disjoint_ab) )

sidecondTests = testGroup "SideCond.sidecond"
               [ test_sidecond_empty
               , test_sidecond_freshonly
               , test_sidecond_one_pre
               , test_sidecond_fresh_exact_ok
               , test_sidecond_fresh_exact_fail
               , test_sidecond_fresh_cover_ok
               , test_sidecond_fresh_cover_fail
               , test_sidecond_fresh_exact_cover_fail
               , test_sidecond_fresh_disjoint
               ]
\end{code}

\subsubsection{Merging Side-Conditions}

\begin{code}
mrgSideCond :: Monad m => SideCond -> SideCond -> m SideCond
mrgSideCond (SC n1 vmap1) (SC n2 vmap2)
 = do let vassoc1 = M.assocs vmap1
      let vassoc2 = M.assocs vmap2
      vassoc <- mrgSCAssoc vassoc1 vassoc2
      sidecond (n1 `S.union` n2) $ M.fromList vassoc
\end{code}

We merge variable by variable:
\begin{code}
mrgSCAssoc [] vassoc2 = return vassoc2
mrgSCAssoc vassoc1 [] = return vassoc1
mrgSCAssoc vassoc1@(va1@(v1,vsc1):rest1)
           vassoc2@(va2@(v2,vsc2):rest2)
  | va1 < va2
    = do varest <- mrgSCAssoc rest1  vassoc2
         return (va1:varest)
  | va1 > va2
    = do varest <- mrgSCAssoc vassoc1  rest2
         return (va2:varest)
  | otherwise -- va1 == va2
    = do vsc' <- mrgVarSideCond vsc1 vsc2
         varest <- mrgSCAssoc rest1 rest2
         return ((v1,vsc'):varest)
\end{code}

\newpage
\subsection{Building side-conditions.}

We want to provide constructors that match how we typically
specify side-condtions, as a conjunction of the following forms:

\begin{eqnarray*}
   x,\lst v   \notin  \fv(T) && \mbox{disjoint}
\\ x,\lst v      =    \fv(T) && \mbox{exact}
\\ x,\lst v \supseteq \fv(T) && \mbox{covering}
\\ x,\lst v \mbox{ fresh}    && \mbox{freshness}
\\ pre      \supseteq \fv(T) && \mbox{pre-condition}
\end{eqnarray*}

All the code below relies on the fact that
\texttt{addDisjSC}, \texttt{addExactSC}, \texttt{addCoverSC},
and \texttt{addPreSC} always succeed
when their last argument is \texttt{vscTrue}.

$\lst v \notin \fv(T)$
\begin{code}
notin :: VarList -> Variable -> SideCond
vl `notin` tV  =  let vsc = fromJust $ addDisjSC (S.fromList vl) vscTrue
                  in SC (S.empty) $ M.fromList [(tV,vsc)]
\end{code}

$\lst v = \fv(T)$
\begin{code}
is :: VarList -> Variable -> SideCond
vl `is` tV  = let vsc = fromJust $ addExactSC (S.fromList vl) vscTrue
              in SC (S.empty) $ M.fromList [(tV,vsc)]
\end{code}

$\lst v \supseteq \fv(T)$
\begin{code}
covers :: VarList -> Variable -> SideCond
vl `covers` tV  = let vsc = fromJust $ addCoverSC (S.fromList vl) vscTrue
                  in SC (S.empty) $ M.fromList [(tV,vsc)]
\end{code}

fresh $\lst v$
\begin{code}
fresh :: VarList -> SideCond
fresh vl  =  SC (S.fromList vl) M.empty
\end{code}

$pre \supseteq \fv(T)$
\begin{code}
pre :: Variable -> SideCond
pre tV  = let  vsc = fromJust $ addPreSC vscTrue
          in SC S.empty $ M.fromList [(tV,vsc)]
\end{code}

This code may fail, however:
\begin{code}
cand :: Monad m => [SideCond] -> m SideCond
cand []        =  return scTrue
cand (sc:scs)  =  do { sc' <- cand scs ; mrgSideCond sc sc' }
\end{code}

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_SideCond :: [TF.Test]
int_tst_SideCond
 = [ testGroup "\nSideCond Internal"
     [ varSCTests
     , sidecondTests
     ]
   ]
\end{code}
