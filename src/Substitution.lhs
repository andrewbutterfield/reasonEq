\section{Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019-22

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
import VarData
import SideCond

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

\textbf{
  We need to augment below with "coverage" cases.
  This is where a substitution target appears in a side-condition
  that states that it covers other variables,
  including the one currently being assessed for substitution.
  We need to plumb side-conditions in here, as well as lists
  of dynamic subscripts.
  We need a substitution context argument
  (side-cond+subscripts+vartables?+?)
}

\begin{code}
substitute :: (Monad m, MonadFail m) => [VarTable] -> Substn -> Term -> m Term
\end{code}
\begin{eqnarray*}
   \vv v \ss {} {v^n} {r^n}  &\defs&  r^i \cond{\vv v=v^i} v,
                                                \mbox{ for one $i \in 1\dots n$}
\\ \vv P \ss {} {v^n} {r^n}
                   &\defs&  r^i \cond{\vv P=v^i} \vv P \ss {} {v^n} {r^n},
                                                                  \mbox{ ditto.}
\end{eqnarray*}
\begin{code}
substitute vts sub@(Substn ts _) vrt@(Var tk v)
  = return $ subsVar vrt v $ S.toList ts
  where
    subsVar vrt v []
      -- we need to handle non-ObsV better!
      | varClass v == ObsV  =  vrt
      | otherwise  =  Sub tk vrt sub
    subsVar vrt v ((tgtv,rplt):rest)
      | v == tgtv  =  rplt
      -- we need cases where v is "covered" by the target
      --  v is x'  and x' is coveredby O$'
      --  tgtv is O$'
      --  rplt is O$_1
      --  we should return  x_1
      | otherwise  =  subsVar vrt v rest
\end{code}
\begin{eqnarray*}
   (\cc i {ts}) \ss {} {v^n} {t^n}
   &\defs&
   (\cc i {ts {\ss {} {v^n} {t^n}}}) \cond{\mathrm{CanSub}(i)} (\cc i {ts}) \ss {} {v^n} {t^n}
\end{eqnarray*}
\begin{code}
substitute vts sub ct@(Cons tk subable i ts)
  | subable  =  do ts' <- sequence $ map (substitute vts sub) ts
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
substitute vts sub bt@(Bnd tk i vs tm)
  = do alpha <- captureAvoidance vs tm sub
       let vs' = S.fromList $ quantsSubst alpha $ S.toList vs
       asub <- substComp vts alpha sub
       tm' <- substitute vts asub tm
       bnd tk i vs' tm'
substitute vts sub lt@(Lam tk i vl tm)
  = do alpha <- captureAvoidance (S.fromList vl) tm sub
       let vl' = quantsSubst alpha vl
       asub <- substComp vts alpha sub
       tm' <- substitute vts asub tm
       lam tk i vl' tm'
\end{code}


Given that we use the \texttt{Sub} term to represent assignment,
we need to treat such seperately:
\begin{code}
substitute vts sub bt@(Sub tk (PVar (PredVar (Identifier ":=" _) _)) _)
  = return $ Sub tk bt sub
\end{code}
\begin{eqnarray*}
   (\ss t {v^m} {t^m}) \ss {} {v^n} {t^n}
   &\defs&
   t (\ss {} {v^m} {t^m};  \ss {} {v^n} {t^n})
\end{eqnarray*}
\begin{code}
substitute vts sub bt@(Sub tk tm s)
  = do sub' <- substComp vts s sub
       substitute vts sub' tm
\end{code}
\begin{eqnarray*}
   (\ii \bigoplus n {lvs}) \ss {} {v^n} {t^n}
   &\defs&
   (\ii \bigoplus n {lvs \ss {} {v^n} {t^n}})
\end{eqnarray*}
\begin{code}
substitute vts (Substn _ lvlvs) bt@(Iter tk sa na si ni lvs)
  = return $ Iter tk sa na si ni $ map (listVarSubstitute (S.toList lvlvs)) lvs
\end{code}
\begin{eqnarray*}
   \kk k \ss {} {v^n} {t^n}   &\defs&  \kk k
\\ \xx n t \ss {} {v^n} {t^n} &\defs& \xx n t
\end{eqnarray*}
\begin{code}
substitute vts sub tm = return tm
\end{code}

\subsubsection{Helper functions}


\begin{code}
captureAvoidance :: (Monad m, MonadFail m) => VarSet -> Term -> Substn -> m Substn
captureAvoidance vs tm sub
  = do let tfv = freeVars tm
       let (tgtvs,rplvs) = substRelFree tfv sub
       let needsRenaming = S.toList (tgtvs `S.intersection` vs)
       let knownVars = theFreeVars ( tfv `mrgFreeVars` rplvs )
       mkFresh knownVars [] [] needsRenaming

mkFresh :: (Monad m, MonadFail m)
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
      -- again, we need to deal with "coverage" cases
      Just t -> error ("quantSubst: non-variable replacement "++trTerm 0 t)

quantSubst atl alvl gv@(LstVar lv)
  = case alookup lv alvl of
      Nothing   ->  gv
      -- again, we need to deal with "coverage" cases
      Just flv  ->  LstVar flv
\end{code}

Used for \texttt{Iter} substitution.
\begin{code}
listVarSubstitute :: [(ListVar,ListVar)] -> ListVar -> ListVar
listVarSubstitute lvlvl lv
  = case alookup lv lvlvl of
      Nothing   ->  lv
      Just lv'  ->  lv'
      -- again, we need to handle "coverage" cases
\end{code}


\newpage
\subsection{Substitution Composition}

Substitution composition ($ \ss {} {v^m} {r^m};  \ss {} {v^n} {r^n}$)
is defined as follows:
\[
\ss {} {v^m} {\ss {r^m} {v^n} {r^n}} \uplus  \ss {} {v^j} {r^j}
\]
where $v^j \notin v^m$.

\begin{code}
substComp :: (Monad m, MonadFail m)
          => [VarTable]
          -> Substn  -- 1st substitution performed
          -> Substn  -- 2nd substitution performed
          -> m Substn
substComp vts (Substn ts1 lvs1) sub2@(Substn ts2 lvs2)
  = do ts' <- varTermCompose vts sub2 (S.toList ts1) (S.toList ts2)
       let lvs' = lvarLVarCompose     (S.toList lvs1) (S.toList lvs2)
       substn ts' lvs'

varTermCompose vts sub2 tl1 tl2
  = do let (vl1,el1) = unzip tl1
       el1' <- sequence $ map (substitute vts sub2) $ el1
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
alphaRename :: (Monad m, MonadFail m)
            => [VarTable]
            -> [(Variable,Variable)]
            -> [(ListVar,ListVar)]
            -> Term
            -> m Term
alphaRename vts vvs lls btm@(Bnd tk n vs tm)
  =  do (vmap,lmap,atm) <- checkAndBuildAlpha vts vvs lls vs tm
        bnd tk n (aRenVS vmap lmap vs) atm
alphaRename vts vvs lls ltm@(Lam tk n vl tm)
  =  do (vmap,lmap,atm) <- checkAndBuildAlpha vts vvs lls (S.fromList vl) tm
        lam tk n (aRenVL vmap lmap vl) atm
alphaRename vts vvs lls trm = fail "alphaRename not applicable"
\end{code}

We have some checks to do, before we apply the $\alpha$-substitution
to the quantifier body.
\begin{code}
checkAndBuildAlpha  :: (Monad m, MonadFail m)
                    => [VarTable]
                    -> [(Variable,Variable)]
                    -> [(ListVar,ListVar)]
                    -> VarSet
                    -> Term
                    -> m ( Map Variable Variable
                         , Map ListVar ListVar
                         , Term )
checkAndBuildAlpha vts vvs lls vs tm
  =  do checkDomain vvs lls vs
        vmap <- injMap vvs
        lmap <- injMap lls
        checkFresh vvs lls tm
        let tvs = map liftReplVar vvs
        sub <- substn tvs lls
        atm <- substitute vts sub tm
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
checkDomain :: (Monad m, MonadFail m) => [(Variable,Variable)]  -- (tgt.v,rpl.v)
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
       else fail "checkDomain: trying to rename free variables."
\end{code}

\newpage
\paragraph{Freshness Checking}~

\begin{code}
checkFresh :: (Monad m, MonadFail m) => ([(Variable,Variable)])  -- (tgt.v,rpl.v)
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
