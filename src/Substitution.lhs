\section{Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Substitution
( substitute
, alphaRename
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

We define a function that applies a substitution to a term.
We also provide a function for $\alpha$-substitution
which checks that a substitution/term pair is of the right form for such a task
(top-level is quantifier, only replacing quantifier variables,
only being replaced by variables only,\dots).


\subsection{Substitution}

Substitution involves three mutually recursive functions
that perform:
term substitution;
$\alpha$-renaming (when substituting into a quantifier);
and substitution composition (when substituting into an explicit substitution).
The latter two then invoke term substitution to do their work.

\newpage
\subsection{Term Substitution}

\begin{code}
substitute :: Monad m => Substn -> Term -> m Term
\end{code}
\begin{eqnarray*}
   \vv v \ss {} {v^n} {t^n}  &\defs&  t^i \cond{\vv v=v^i} v,
                                                \mbox{ for one $i \in 1\dots n$}
\\ \vv P \ss {} {v^n} {t^n}
                   &\defs&  t^i \cond{\vv P=v^i} \vv P \ss {} {v^n} {t^n},
                                                                  \mbox{ ditto.}
\end{eqnarray*}
\begin{code}
substitute sub@(Substn ts _) vrt@(Var tk v)
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
substitute sub ct@(Cons tk subable i ts)
  | subable  =  do ts' <- sequence $ map (substitute sub) ts
                   return $ Cons tk subable i ts'
  | otherwise  =  return $ Sub tk ct sub
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
substitute sub bt@(Bnd tk i vs tm)
  = do alpha <- captureAvoidance vs tm sub
       let vs' = S.fromList $ quantsSubst alpha $ S.toList vs
       asub <- substComp alpha sub
       tm' <- substitute asub tm
       bnd tk i vs' tm'
substitute sub lt@(Lam tk i vl tm)
  = do alpha <- captureAvoidance (S.fromList vl) tm sub
       let vl' = quantsSubst alpha vl
       asub <- substComp alpha sub
       tm' <- substitute asub tm
       lam tk i vl' tm'
\end{code}
\newpage
\begin{eqnarray*}
   (\ss t {v^m} {t^m}) \ss {} {v^n} {t^n}
   &\defs&
   t (\ss {} {v^m} {t^m};  \ss {} {v^n} {t^n})
\end{eqnarray*}
\begin{code}
substitute sub bt@(Sub tk tm s)
  = do sub' <- substComp s sub
       substitute sub' tm
\end{code}
\begin{eqnarray*}
   (\ii \bigoplus n {lvs}) \ss {} {v^n} {t^n}
   &\defs&
   (\ii \bigoplus n {lvs \ss {} {v^n} {t^n}})
\end{eqnarray*}
\begin{code}
substitute (Substn _ lvlvs) bt@(Iter tk sa na si ni lvs)
  = return $ Iter tk sa na si ni $ map (listVarSubstitute (S.toList lvlvs)) lvs
\end{code}
\begin{eqnarray*}
   \kk k \ss {} {v^n} {t^n}   &\defs&  \kk k
\\ \xx n t \ss {} {v^n} {t^n} &\defs& \xx n t
\end{eqnarray*}
\begin{code}
substitute sub tm = return tm
\end{code}

Helper functions.


\begin{code}
captureAvoidance :: Monad m => VarSet -> Term -> Substn -> m Substn
captureAvoidance vs tm sub
  = do let tfv = freeVars tm
       let (tgtvs,rplvs) = substRelFree tfv sub
       let needsRenaming = S.toList (tgtvs `S.intersection` vs)
       let knownVars = theFreeVars ( tfv `mrgFreeVars` rplvs )
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
(Identifier i u) `idNumAdd` n = fromJust $ uident i (u+n)
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
substComp :: Monad m
          => Substn  -- 1st substitution performed
          -> Substn  -- 2nd substitution performed
          -> m Substn
substComp (Substn ts1 lvs1) sub2@(Substn ts2 lvs2)
  = do ts' <- varTermCompose sub2 (S.toList ts1) (S.toList ts2)
       let lvs' = lvarLVarCompose     (S.toList lvs1) (S.toList lvs2)
       substn ts' lvs'

varTermCompose sub2 tl1 tl2
  = do let (vl1,el1) = unzip tl1
       el1' <- sequence $ map (substitute sub2) $ el1
       let tl1' = zip vl1 el1'
       let tl2' = tl2 `strip1` vl1
       return (tl1' ++ tl2')

strip1 :: Eq a => [(a,b)] -> [a] -> [(a,b)]
strip1 [] _ = []
strip1 (xy@(x,y):xys) xs
  | x `elem` xs  =  strip1 xys xs
  | otherwise    =  xy : strip1 xys xs

lvarLVarCompose lvlv1 lvlv2
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
\begin{code}
alphaRename :: Monad m => [(Variable,Variable)]
                       -> [(ListVar,ListVar)]
                       -> Term
                       -> m Term
alphaRename vvs lls btm@(Bnd tk n vs tm)
  =  do (vmap,lmap,atm) <- checkAndBuildAlpha vvs lls vs tm
        bnd tk n (aRenVS vmap lmap vs) atm
alphaRename vvs lls ltm@(Lam tk n vl tm)
  =  do (vmap,lmap,atm) <- checkAndBuildAlpha vvs lls (S.fromList vl) tm
        lam tk n (aRenVL vmap lmap vl) atm
alphaRename vvs lls trm = fail "alphaRename not applicable"
\end{code}

We have some checks to do, before we apply the $\alpha$-substitution
to the quantifier body.
\begin{code}
checkAndBuildAlpha :: Monad m => [(Variable,Variable)]
                              -> [(ListVar,ListVar)]
                              -> VarSet
                              -> Term
                              -> m ( Map Variable Variable
                                   , Map ListVar ListVar
                                   , Term )
checkAndBuildAlpha vvs lls vs tm
  =  do checkDomain vvs lls vs
        vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        let tvs = map liftReplVar vvs
        sub <- substn tvs lls
        atm <- substitute sub tm
        return (vmap,lmap,atm)
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


\paragraph{Domain Checking}~

\begin{code}
checkDomain :: Monad m => [(Variable,Variable)]  -- (tgt.v,rpl.v)
                       -> [(ListVar,ListVar)]    -- (tgt.lv,rpl.lv)
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

\newpage
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
   in if S.null (theFreeVars trmFV `S.intersection` alphaRng)
       then return ()
       else fail "alphaRename: new bound-vars not fresh"
\end{code}

\paragraph{Lifting Replacement Variable to Term}~

\begin{code}
liftReplVar :: (Variable,Variable) -> (Variable,Term)
liftReplVar (tgtv,rplv) = (tgtv,varAsTerm rplv)
\end{code}


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
