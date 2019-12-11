\section{Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Substitution
( SubAbility(..)
, SubAbilityMap, SubAbilityMaps
, substitute
) where
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List
import Data.Maybe

import Utilities (alookup,injMap)
import LexBase
import Variables
import AST
import FreeVars
import TestRendering

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

\subsection{Introduction}

We define the notion of ``substitutability''
and provide a function that applies a substitution to a term.
We also provide a function for $\alpha$-substitution
which checks that a substitution/term pair is of the right form for such a task
(top-level is quantifier, only replacing quantifier variables,
only being replaced by variables only,\dots).

\newpage
\subsection{Substitutability}

In order to do this, we need to know which constructors are substitutable
(e.g, propositional operators, and UTP conditional $\_\cond{\_}\_$ are,
while assignment  $\_:=\_$ is not).
We explicitly capture this property:
\begin{code}
data SubAbility = CS -- Can Substitute
              | NS -- Not Substitutable
              deriving (Eq, Ord, Show, Read)
\end{code}
We maintain, per-theory,
a map from  \texttt{Cons} identifiers defined by that theory,
to their subsitutability.
In any given proof context we will have a list of such maps,
one for each theory in scope.
\begin{code}
type SubAbilityMap = Map Identifier SubAbility
type SubAbilityMaps = [SubAbilityMap]
\end{code}
We want to search a list of these maps, checking for substitutability
\begin{code}
getSubstitutability :: Monad m => SubAbilityMaps -> Identifier -> m SubAbility
getSubstitutability [] n  =  fail ("No substitutability defined for "++trId n)
getSubstitutability (sam:sams) n
  = case M.lookup n sam of
      Nothing  ->  getSubstitutability sams n
      Just s   ->  return s
\end{code}


We also want to convert our $\alpha$ ``maps'' into
substitutions, when we encounter a non-substitutable constructor.
\begin{code}
alphaAsSubstn :: (Map Variable Variable)  -- (tgt.v -> rpl.v)
              -> (Map ListVar ListVar)    -- (tgt.lv -> rpl.lv)
              -> Substn
alphaAsSubstn vmap lmap
  = fromJust $ substn (M.assocs $ M.map varAsTerm vmap) $ M.assocs lmap
\end{code}


\subsection{Substitution}

Substitution involves three mutally recursive functions
that perform:
term substitution;
$\alpha$-renaming (when substituting into a quantifier);
and substitution composition (when substituting into an explicit substitution).
The latter two then invoke term substitution to do their work.

\newpage
\subsection{Term Substitution}

\begin{code}
substitute :: Monad m => [SubAbilityMap] -> Substn -> Term -> m Term
\end{code}
\begin{eqnarray*}
   \vv v \ss {} {v^n} {t^n}  &\defs&  t^i \cond{\vv v=v^i} v,
                                                \mbox{ for one $i \in 1\dots n$}
\\ \vv P \ss {} {v^n} {t^n}
                   &\defs&  t^i \cond{\vv P=v^i} \vv P \ss {} {v^n} {t^n},
                                                                  \mbox{ ditto.}
\end{eqnarray*}
\begin{code}
substitute _ sub@(Substn ts _) vrt@(Var tk v)
  = return $ subsVar vrt v $ S.toList ts
  where
    subsVar vrt v []
      | varClass v == ObsV  =  vrt
      | otherwise  =  Sub tk vrt sub
    subsVar vrt v ((tgtv,rplt):rest)
      | v == tgtv  =  rplt
      | otherwise  =  subsVar vrt v rest
\end{code}
\begin{eqnarray*}
   (\cc i {ts}) \ss {} {v^n} {t^n}
   &\defs&
   (\cc i {ts {\ss {} {v^n} {t^n}}}) \cond{\mathrm{CanSub}(i)} (\cc i {ts}) \ss {} {v^n} {t^n}
\end{eqnarray*}
\begin{code}
substitute sams sub ct@(Cons tk i ts)
  = do sbl <- getSubstitutability sams i
       if sbl == NS
        then return $ Sub tk ct sub
        else do ts' <- sequence $ map (substitute sams sub) ts
                return $ Cons tk i ts'
\end{code}
\begin{eqnarray*}
   (\bb n {x^+} t) \ss {} {v^n} {t^n}
   &\defs&
   (\bb n {x^+\alpha} {t\alpha \ss {} {v^j} {t^j}}), \quad v^j \notin x^+
\\ (\ll n {x^+} t) \ss {} {v^n} {t^n}
   &\defs&
   (\ll n {x^+\alpha} {t\alpha \ss {} {v^j} {t^j}}), \quad v^j \notin x^+
\\ \alpha &\defs&  x^j \mapsto \nu^j, \quad
   x^j \in \fv(t^i) \land \nu \mbox{ fresh.}
\end{eqnarray*}
\begin{code}
substitute sams sub bt@(Bnd tk i vs tm)
  = do alpha <- captureAvoidance vs tm sub
       let vs' = S.fromList $ quantsSubst alpha $ S.toList vs
       asub <- substComp sams alpha sub
       tm' <- substitute sams asub tm
       bnd tk i vs' tm'
substitute sams sub lt@(Lam tk i vl tm)
  = do alpha <- captureAvoidance (S.fromList vl) tm sub
       let vl' = quantsSubst alpha vl
       asub <- substComp sams alpha sub
       tm' <- substitute sams asub tm
       lam tk i vl' tm'
\end{code}
\newpage
\begin{eqnarray*}
   (\ss t {v^m} {t^m}) \ss {} {v^n} {t^n}
   &\defs&
   t (\ss {} {v^m} {t^m};  \ss {} {v^n} {t^n})
\end{eqnarray*}
\begin{code}
substitute sams sub bt@(Sub tk tm s)
  = do sub' <- substComp sams s sub
       substitute sams sub' tm
\end{code}
\begin{eqnarray*}
   (\ii \bigoplus n {lvs}) \ss {} {v^n} {t^n}
   &\defs&
   (\ii \bigoplus n {lvs \ss {} {v^n} {t^n}})
\end{eqnarray*}
\begin{code}
substitute sams (Substn _ lvlvs) bt@(Iter tk na ni lvs)
  = return $ Iter tk na ni $ map (listVarSubstitute (S.toList lvlvs)) lvs
\end{code}
\begin{eqnarray*}
   \kk k \ss {} {v^n} {t^n}   &\defs&  \kk k
\\ \xx n t \ss {} {v^n} {t^n} &\defs& \xx n t
\end{eqnarray*}
\begin{code}
substitute sams sub tm = return tm
\end{code}

Helper functions.


\begin{code}
captureAvoidance :: Monad m => VarSet -> Term -> Substn -> m Substn
captureAvoidance vs tm sub
  = do let tfv = freeVars tm
       let (tgtvs,rplvs) = substRelFree tfv sub
       let needsRenaming = S.toList (tgtvs `S.intersection` vs)
       let knownVars = tfv `S.union` rplvs
       mkFresh knownVars [] [] needsRenaming

mkFresh :: Monad m
        => VarSet
        -> [(Variable,Term)]
        -> [(ListVar,ListVar)]
        -> VarList -> m Substn
mkFresh _ vts lvlvs [] = substn vts lvlvs

mkFresh knVars vts lvlvs (StdVar v : needsRenm)
  =  mkFresh knVars ((v,varAsTerm $ freshV knVars 2 v):vts) lvlvs needsRenm

mkFresh knVars vts lvlvs (LstVar lv : needsRenm)
  =  mkFresh knVars vts          ((lv,freshLV knVars 2 lv):lvlvs) needsRenm

freshV :: VarSet -> Int -> Variable -> Variable
freshV knVars n v@(Vbl i vc vw)
  | StdVar nv `S.member` knVars  =  freshV knVars (n+1) v
  | otherwise             =  nv
  where nv = Vbl (i `idNumAdd` n) vc vw

freshLV :: VarSet -> Int -> ListVar -> ListVar
freshLV knVars n lv@(LVbl (Vbl i vc vw) is js)
  | LstVar nlv `S.member` knVars  =  freshLV knVars (n+1) lv
  | otherwise             =  nlv
  where nlv = LVbl (Vbl (i `idNumAdd` n) vc vw) is js

idNumAdd :: Identifier -> Int -> Identifier
(Identifier i) `idNumAdd` n = fromJust $ ident (i++show n)
\end{code}

\newpage
This code assumes that \texttt{alpha} was produced by \texttt{captureAvoidance}.
\begin{code}
quantsSubst :: Substn -> VarList -> VarList
quantsSubst (Substn ats alvs) vl
  = map (quantSubst (S.toList ats) (S.toList alvs)) vl

quantSubst :: [(Variable,Term)] -> [(ListVar,ListVar)] -> GenVar -> GenVar
quantSubst atl alvl gv@(StdVar v)
  = case alookup v atl of
      Nothing          ->  gv
      Just (Var _ fv)  ->  StdVar fv
      Just t -> error ("quantSubst: non-variable replacement "++trTerm 0 t)

quantSubst atl alvl gv@(LstVar lv)
  = case alookup lv alvl of
      Nothing   ->  gv
      Just flv  ->  LstVar flv
\end{code}

Used for \texttt{Iter} substitution.
\begin{code}
listVarSubstitute :: [(ListVar,ListVar)] -> ListVar -> ListVar
listVarSubstitute lvlvl lv
  = case alookup lv lvlvl of
      Nothing   ->  lv
      Just lv'  ->  lv'
\end{code}


\newpage
\subsection{Substitution Composition}

Substitution composition ($ \ss {} {v^m} {t^m};  \ss {} {v^n} {t^n}$)
is defined as follows:
\[
\ss {} {v^m} {\ss {t^m} {v^n} {t^n}} \uplus  \ss {} {v^j} {t^j}
\]
where $v^j \notin v^m$.

\begin{code}
substComp :: Monad m => [SubAbilityMap]
          -> Substn  -- 1st substitution performed
          -> Substn  -- 2nd substitution performed
          -> m Substn
substComp sams (Substn ts1 lvs1) sub2@(Substn ts2 lvs2)
  = do ts' <- varTermCompose sams sub2 (S.toList ts1) (S.toList ts2)
       let lvs' = lvarLVarCompose sams     (S.toList lvs1) (S.toList lvs2)
       substn ts' lvs'

varTermCompose sams sub2 tl1 tl2
  = do let (vl1,el1) = unzip tl1
       el1' <- sequence $ map (substitute sams sub2) $ el1
       let tl1' = zip vl1 el1'
       let tl2' = tl2 `strip1` vl1
       return (tl1' ++ tl2')

strip1 :: Eq a => [(a,b)] -> [a] -> [(a,b)]
strip1 [] _ = []
strip1 (xy@(x,y):xys) xs
  | x `elem` xs  =  strip1 xys xs
  | otherwise    =  xy : strip1 xys xs

lvarLVarCompose sams lvlv1 lvlv2
  = let
     (tlv1,rlv1) = unzip lvlv1
     rlv1' = map (lvSubstitute lvlv2) rlv1
     lvlv1' = zip tlv1 rlv1'
     lvlv2' = lvlv2 `strip1` tlv1
    in lvlv1' ++ lvlv2'

lvSubstitute ((tlv2,rlv2):lv2lv) rlv
  | rlv == tlv2      =  rlv2
  | otherwise        =  lvSubstitute lv2lv rlv
lvSubstitute [] rlv  =  rlv
\end{code}

\newpage
\subsection{$\alpha$-Substitution}

We will have checks and balances for when $\alpha$-substitution is invoked
from outside.
The term substitution function will pass these checks and so will invoke it
directly, as a term substitution with a carefully crafted substitution.
\begin{code}
-- KEEP THIS FOR ALPHA CORRECTNESS CHECKS
-- alphaRename sams vvs lls (Bnd tk n vs tm)
--   =  do checkDomain vvs lls vs
--         vmap <- injMap vvs
--         lmap <- injMap lls
--         checkFresh vvs lls tm
--         bnd tk n (aRenVS vmap lmap vs) (aRenTRM sams vmap lmap tm)
-- alphaRename sams vvs lls (Lam  tk n vl tm)
--   =  do checkDomain vvs lls (S.fromList vl)
--         vmap <- injMap vvs
--         lmap <- injMap lls
--         checkFresh vvs lls tm
--         lam tk n (aRenVL vmap lmap vl) (aRenTRM sams vmap lmap tm)
-- alphaRename sams vvs lls trm = fail "alphaRename not applicable"
\end{code}

\paragraph{Domain Checking}~

\begin{code}
checkDomain :: Monad m => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                       -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                       -> VarSet
                       -> m ()
checkDomain vvs lls qvs
 = let
     alphaDom = (S.fromList $ map (StdVar . fst) vvs)
                `S.union`
                (S.fromList $ map (LstVar . fst) lls)
   in if S.null (alphaDom S.\\ qvs)
       then return ()
       else fail "alphaRename: trying to rename free variables."
\end{code}

\paragraph{Freshness Checking}~

\begin{code}
checkFresh :: Monad m => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
                      -> [(ListVar,ListVar)]      -- (tgt.lv,rpl.lv)
                      -> Term
                      -> m ()
checkFresh vvs lls trm
 = let
     trmFV = freeVars trm
     alphaRng = (S.fromList $ map (StdVar . snd) vvs)
                `S.union`
                (S.fromList $ map (LstVar . snd) lls)
   in if S.null (trmFV `S.intersection` alphaRng)
       then return ()
       else fail "alphaRename: new bound-vars not fresh"
\end{code}

\newpage
\paragraph{$\mathbf\alpha$-Renaming (many) Variables}~

\begin{code}
aRenVS vmap lmap  =  S.fromList . aRenVL vmap lmap . S.toList

aRenVL vmap lmap vl = map (aRenGV vmap lmap) vl

aRenGV vmap lmap (StdVar  v)  =  StdVar $ aRenV  vmap v
aRenGV vmap lmap (LstVar lv)  =  LstVar $ aRenLV lmap lv

aRenV vmap v
  = case M.lookup v vmap of
      Nothing   ->  v
      Just v'   ->  v'

aRenLV lmap lv
  = case M.lookup lv lmap of
      Nothing   ->  lv
      Just lv'  ->  lv'
\end{code}

\newpage
\paragraph{$\mathbf\alpha$-Renaming Terms}
Top-level quantifier body and below.

Variables and and iterators are straightforward
\begin{code}
aRenTRM sams vmap lmap (Var  tk v)     =  fromJust $ var tk (aRenV vmap v)
aRenTRM sams vmap lmap (Iter tk na ni lvs)  =   Iter tk na ni $ map (aRenLV lmap) lvs
\end{code}
We need to check constructors for substitutability
\begin{code}
aRenTRM sams vmap lmap tm@(Cons tk n ts)
  = case getSubstitutability sams n of
      Just CS  ->  Cons tk n $ map (aRenTRM sams vmap lmap) ts
      _        ->  Sub tk tm $ alphaAsSubstn vmap lmap
\end{code}
Internal quantifiers screen out renamings%
\footnote{We wouldn't need this if we guaranteed no quantifier shadowing.}
.
\[
   (\mathsf{Q} V \bullet P)\alpha
   =
   (\mathsf{Q} V \bullet P(\alpha\setminus V))
\]
\begin{code}
aRenTRM sams vmap lmap (Bnd tk n vs tm)
 = fromJust $ bnd tk n vs (aRenTRM sams vmap' lmap' tm)
 where vmap' = vmap `M.withoutKeys` (stdVarSetOf vs)
       lmap' = lmap `M.withoutKeys` (listVarSetOf vs)

aRenTRM sams vmap lmap (Lam  tk n vl tm)
 = fromJust $ lam tk n vl (aRenTRM sams vmap' lmap' tm)
 where vs = S.fromList vl
       vmap' = vmap `M.withoutKeys` (stdVarSetOf vs)
       lmap' = lmap `M.withoutKeys` (listVarSetOf vs)
\end{code}
Substitution is tricky \dots
\[
  (P[\lst e/\lst x])\alpha
  =
  (P(\alpha\setminus\lst x)[\lst e \alpha / \lst x]
\]
\begin{code}
aRenTRM sams vmap lmap (Sub tk tm (Substn ts lvs))
  = let

      (vl,tl) = unzip $ S.toList ts
      tl' = map (aRenTRM sams vmap lmap) tl
      tsl' = zip vl tl'

      (tvl,rvl) = unzip $ S.toList lvs
      rvl' = map (aRenLV lmap) rvl
      lvsl' = zip tvl rvl'

      suba = fromJust $ substn tsl' lvsl'

      subtgtvs  = S.fromList vl
      vmap' = vmap `M.withoutKeys` subtgtvs

      subtgtlvs = S.fromList tvl
      lmap' = lmap `M.withoutKeys` subtgtlvs

    in Sub tk (aRenTRM sams vmap' lmap' tm) suba
\end{code}
Everything else is unaffected.
\begin{code}
aRenTRM _ _ _ trm = trm  -- Val, Cls
\end{code}
