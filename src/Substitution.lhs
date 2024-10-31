\chapter{Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019-24

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Substitution
( SubContext, mkSubCtxt, subContext0
, substitute
-- test stuff below
, int_tst_Subst
) where
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List
import Data.Maybe
import Control.Applicative

import Utilities (alookup,injMap)
import Control (mapfst,mapsnd)
import UnivSets
import LexBase
import Variables
import AST
import SideCond
import FreeVars
import VarData

import TestRendering

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}

\newpage

\section{Introduction}

We define a function that applies a substitution to a term.
We also provide functions for $\alpha$-substitution
and substitution composition.

Substitution here is not simple, because we have list variables
that can represent either arbitrary sets/lists of variables,
or very specific sets/lists of variables.
The latter can be determined from known variable data,
as well as side-conditions.
We also have the complication of variable temporality that needs to be handled.

\subsection{Temporal Uniformity}

The treatment of side-conditions talks about ``temporal disjointness''.
This also an important concept where substitution is involved:
\begin{itemize}
\item
A term is \emph{temporally uniform} 
if all free variables have the same temporality.
\item
A list of variables is \emph{temporally uniform} 
if all the variables have the same temporality.
\item
A list of terms is \emph{temporally uniform} 
if all the terms are temporally uniform and  have the same temporality.
\item
A substitution is \emph{temporally uniform} 
if the target variable list
% \footnote{This is the catenation of both standard and list variables}%
is temporally uniform, 
and the replacement list is temporally uniform.
\end{itemize}
We can formalise this as follows, 
where $VW=\setof{before,during(m),after}$
and we have $when : V \fun VW$:
\begin{eqnarray*}
   temp &:& T \fun \power (VW)
\\ temp(\vv v) &\defs& \setof{when(\vv v)}
\\ temp(\cc n {ts}) &\defs& \bigcup_{t \in ts} temp(t)
\\  &\vdots&
\end{eqnarray*} 
\begin{code}
termTemp :: Term -> Set VarWhen
termTemp = S.map gvarWhen . theFreeVars . freeVars scTrue -- safe?
gvarTemp :: GenVar -> Set VarWhen
gvarTemp gv = S.singleton $ gvarWhen gv
listTemp :: Ord a => (a -> Set VarWhen) -> [a] -> Set VarWhen
listTemp aTemp = S.unions . map aTemp
substTemp :: Substn 
          -> ( Set VarWhen    -- target temporality
             , Set VarWhen )  -- replacement temporality
substTemp (Substn tvs lvlvs)
  = let 
      (vs,ts)     = unzip $ S.toList tvs
      (tlvs,rlvs) = unzip $ S.toList lvlvs
    in ( S.fromList (map varWhen vs ++ map lvarWhen tlvs)
       , S.unions (map termTemp ts)
         `S.union`
         S.fromList (map lvarWhen rlvs) 
       )      
\end{code}
\begin{eqnarray*}
   utemp &:& VW \fun \Bool
\\ utemp(W) &\defs& \#(W)=1
\\ utemp_T &:& T \fun \Bool
\\ utemp_T &\defs& utemp(temp(t))
\\ utemp_{T^*} &:& T^* \fun \Bool
\\ utemp_{T^*}(ts) &\defs& utemp(\bigcup_{t \in ts} utem_T(v))
\\ utemp_{VL} &:& V^* \fun \Bool
\\ utemp_{VL}(vs) &\defs& utemp(\bigcup_{v \in vs} when(v))
\end{eqnarray*} 
We define a monadic function that returns the unique temporality,
if it exists:
\begin{code}
theTemp :: MonadFail m => Set VarWhen -> m VarWhen
theTemp ws 
  = case S.toList ws of
      [w]  ->  return w
      _    ->  fail ("no unique temporality")
\end{code}

Now, consider a general substitution $e[\lst r/\lst x]$.
We find that if $e$ and the $\lst x$ are temporally uniform,
with different temporalities, then the outcome is just $e$.
In any other case there are no simplifications.
\begin{code}
tempSubMiss :: Term -> Substn -> Bool
tempSubMiss tm sub
  = case ( theTemp $ termTemp tm, theTemp $ fst $ substTemp sub ) of
      (Just tmw, Just subtw ) -> tmw /= subtw
      _ -> False
\end{code}

\subsection{Target Completeness}

There are two main sources of substitution in UTP: 
for a few variables in assignments,
and for all the observation variables in sequential composition.
These drill down to substitutions that look like:
$$f_1[e,O\less x/x_1,O_1\less x]$$
Here the target covers all observations $O_1$, 
and we consider $f_1$ to be a variable, representing an arbitrary term.
We want the outcome to be $f$.
Similarly, we expect this to work for other temporality combinations, e.g.:
$$f'[e_1,O_1\less x/x',O'\less x] = f_1$$
We have uniform temporalites, 
with the term and target having the same temporality,
but also, we have that the target covers the whole observation space of $f$,
which is denoted by the (uniform) side-condition $O \supseteq f$.

We need to be able to check when a target-list is complete.
This means that all the target variables denote distinct variables,
or variable-sets, and they cover the whole space ($O$).
We assume, for simplicity,
that all standard variables are in $O$, 
and list variables are of the form $O\less{vs}$,
where $vs$ contains only standard variables.
In general we see a list like:
$$
[x_1,\dots,x_n,O\less{xs_1},\dots,O\less{xs_m}]
\text{ where }
vs_i = \setof{xs_{i1},\dots,xs_{ik_i}}
$$
For disjointness we can make two observations:
\begin{itemize}
\item
For all $i$, $\setof{x_1,\dots,x_n}\subseteq vs_i$, 
\item
For any $xs_i$ and $xs_j$, $xs_i \cup xs_j = O$.
\end{itemize}
In theories with known fixed alphabets, these are all easy to check.
When doing general proofs for all theories,
we cannot verify the second observation.
For now we only support the case where $m=1$:
$$
[x_1,\dots,x_n,O\less{x_1,\dots,x_n}]
$$
Reminder: we require temporal uniformity as well.
If we have a complete substitution we want to know the target temporality.
\textbf{NOTE: 
 not used anywhere but similar code appears in \h{uniformSubstitute} below.
 }
\begin{code}
isCompleteSubst :: MonadFail m => Substn -> m VarWhen
isCompleteSubst (Substn ts lvs) = isCompSubst (S.toList ts) (S.toList lvs)
isCompSubst ts [(tlv@(LVbl v lessids []),_)]
  |  tids /= lessids    =  fail "targets not disjoint"
  |  length whns' /= 1  =  fail "targets not uniform"
  |  twh /= varWhen v   =  fail "listvar temporality differs"
  |  otherwise          =  return twh
  where
    getIdWhen (Vbl idnt _ whn) = (idnt,whn)
    (tids,whns) = unzip $ map (getIdWhen . fst) ts
    whns' = nub whns
    twh = head whns
isCompSubst _ _ = fail "too complicated to check completeness"
\end{code}

\subsection{Substitution Contexts}

All substitutions need a context argument that describes the following
aspects of the current state of a proof:
\begin{itemize}
  \item side-conditions
  \item list-var variable data
\end{itemize}
\begin{code}
data SubContext
  = SubCtxt { subSC :: SideCond
            , subVD :: [VarTable]
            }
  deriving (Eq,Show)

mkSubCtxt = SubCtxt

subContext0 = mkSubCtxt scTrue []
\end{code}

\newpage
\section{Term Substitution}

\begin{code}
substitute :: (MonadFail m, Alternative m) 
           => SubContext -> Substn -> Term -> m Term
\end{code}
We first note that $P[/] = P$:
\begin{code}
substitute _ sub tm | isNullSubstn sub  =  return tm
\end{code}

\subsection{Variable Term Substitution}

We are dealing with the case $\vv v \ss {} {g^n} {r^n}$,
where $v$ denotes a standard variable. 
\begin{code}
substitute sctx@(SubCtxt sc vdata) sub@(Substn vts lvlvs) vrt@(Var tk v)
\end{code}

We first scan the var-term pairs looking for $\vv v$,
returning the replacement if found:
\begin{code}
-- substitute sctx@(SubCtxt sc vdata) sub@(Substn vts lvlvs) vrt@(Var tk v)
  =  let vtl = S.toList vts ; lvlvl = S.toList lvlvs in
-- we should also use vdata to "expand" sc here
     alookup v vtl
\end{code}
Next we scan the list-variable  pairs, with the side-conditions in hand,
looking for a list-variable that covers $\vv v$:
\begin{code}
-- substitute sctx@(SubCtxt sc vdata) sub@(Substn vts lvlvs) vrt@(Var tk v)
--   let vtl = S.toList vts ; lvlvl = S.toList lvlvs in
     <|> lvlvlSubstitute sctx vrt lvlvl
\end{code}
Then we see if we have a uniform substitution, 
provided that $\vv v$ is dynamic:
\begin{code}
-- substitute sctx@(SubCtxt sc vdata) sub@(Substn vts lvlvs) vrt@(Var tk v)
--   let vtl = S.toList vts ; lvlvl = S.toList lvlvs in
     <|> uniformSubstitute sctx vrt vtl lvlvl
\end{code}
If nothing is found we return the substitution unchanged:
\begin{code}
-- substitute sctx@(SubCtxt sc vdata) sub@(Substn vts lvlvs) vrt@(Var tk v)
     <|> pure (Sub tk vrt sub)
  where
\end{code}




\subsection{Cons-Term Substitution}

\begin{eqnarray*}
   (\cc i {ts}) \ss {} {v^n} {t^n}
   &\defs&
   ( \cc i {ts {\ss {} {v^n} {t^n}}}) 
     \cond{\mathrm{CanSub}(i)} 
   (\cc i {ts}) \ss {} {v^n} {t^n}
\end{eqnarray*}
\begin{code}
substitute sctx sub ct@(Cons tk subable i ts)
  | subable    =  do ts' <- sequence $ map (substitute sctx sub) ts
                     return $ Cons tk subable i ts'
  | otherwise  =     return $ Sub tk ct sub
\end{code}

\newpage
\subsection{Binding-Term Substitution}

Given $(\bb n {x^+} t) \ss {} {v^n} {t^n}$,
we do the following:
\begin{enumerate}
\item
  Remove substitution pairs where the target variable $v_i \in x^+$,
  to give \emph{effective substitution} $[t^k/v^k]$.  
  If $k=0$ we can stop here and return the quantifier term unchanged.
\item 
  Compute an $\alpha$-substitution that maps $x_i$ to fresh $\nu_i$,
  for all $x_i \in \fv(t^k)$.
\item
  Construct $\bb n {x^+\alpha} {t\alpha \ss {} {v^k} {t^k}}$.
\end{enumerate}
We handle $(\ll n {x^+} t) \ss {} {v^n} {t^n}$ in a similar fashion.
\begin{code}
substitute sctx sub bt@(Bnd tk i vs tm)
  | isNullSubstn effsub  =  return bt
  | otherwise 
    = do  alpha <- captureAvoidance (subSC sctx) vs tm effsub
          let vs' = S.fromList $ quantsSubst alpha $ S.toList vs
          asub <- substComp alpha effsub --- succeeds as alpha is var-only
          tm' <- substitute sctx asub tm
          bnd tk i vs' tm'
  where
    effsub = computeEffSubst vs sub
--  effsubst = computeEffSubst sctx vs sub
--  if null effsubset then return bt else ....
substitute sctx sub lt@(Lam tk i vl tm)
  | isNullSubstn effsub  =  return lt
  | otherwise 
    = do  alpha <- captureAvoidance (subSC sctx) vs tm effsub
          let vl' = quantsSubst alpha vl
          asub <- substComp alpha effsub --- succeeds as alpha is var-only
          tm' <- substitute sctx asub tm
          lam tk i vl' tm'
  where
    vs = S.fromList vl
    effsub = computeEffSubst vs sub
\end{code}

\subsection{Iteration Substitution}

\begin{eqnarray*}
   (\ii \bigoplus n {lvs}) \ss {} {v^n} {t^n}
   &\defs&
   (\ii \bigoplus n {lvs \ss {} {v^n} {t^n}})
\end{eqnarray*}
\begin{code}
substitute sctx (Substn _ lvlvs) bt@(Iter tk sa na si ni lvs)
  = return $ Iter tk sa na si ni
           $ map (listVarSubstitute sctx (S.toList lvlvs)) lvs
\end{code}


\newpage
\subsection{Substitution-Term Substitution}

\subsubsection{Assignment Substitution}

Given that we use the \texttt{Sub} term to represent assignment,
we need to treat such seperately, noting that it is n.s.::
\begin{eqnarray*}
   (x:=e)[t^n/v^v] &=& (x:=e)[t^n/v^v]
\end{eqnarray*}
\begin{code}
substitute sctx sub st@(Sub tk bt _)
  | isAssignment bt  =  return $ Sub tk st sub
\end{code}


\subsubsection{Substitution Substitution}

\begin{eqnarray*}
   (\ss t {v^m} {t^m}) \ss {} {v^n} {t^n}
   &\defs&
     {t (\ss {} {v^m} {t^m};  \ss {} {v^n} {t^n})}
     \quad \text{if } \ss {} {v^m} {t^m};  \ss {} {v^n} {t^n} \text{ defined}
\end{eqnarray*}
\begin{code}
substitute sctx sub bt@(Sub tk tm s)
  = case substComp s sub of
     Just sub' -> substitute sctx sub' tm
     Nothing   -> return $ Sub tk bt sub
\end{code}


\subsection{Non-Substitutable Terms}

\begin{eqnarray*}
   \kk k \ss {} {v^n} {t^n}   &\defs&  \kk k
\\ \xx n t \ss {} {v^n} {t^n} &\defs& \xx n t
\end{eqnarray*}
\begin{code}
substitute sctx sub tm = return tm
\end{code}

\newpage 
\subsection{Helper Functions}

\subsubsection{Does a list-variable cover the standard variable?}


What we try next is to scan the list-var substitutions 
($\setof{\dots,(\ell^T/\ell^R),\dots$})
asking the following questions:
\begin{enumerate}
  \item Is $v$ definitely in some $\ell^T$?  
        If so, note \emph{the} relevant $(\ell^T,\ell^R)$ pair,
        and exit the scan.
  \item Is $v$ definitely not in $\ell^T$ ?
        If so, skip and move on.
  \item Otherwise, $v$ might be in $\ell^T$,
        so add the relevant $(\ell^T,\ell^R)$ pair to a list
\end{enumerate}
We will get the following outcomes: 
we either have one applicable substitution pair, 
or a list of zero or more possible substitutions.
\begin{enumerate}
  \item Found definite pair $(\ell^T,\ell^R)$?
    Return $v$ modified as follows: 
\begin{eqnarray*}
   \prv v \ss{}{\prv\ell}{\dyn\ell}  &=&  \dyn v ~~\IF~~ \prv\ell \supseteq \prv v
\\ \psv v \ss{}{\psv\ell}{\dyn\ell}  &=&  \dyn v ~~\IF~~ \psv\ell \supseteq \psv v
\\ v_d    \ss{}{\ell_d}  {\dyn\ell}  &=&  \dyn v ~~\IF~~ \ell_d \supseteq v_d
\end{eqnarray*}
  \item Have empty list of possible substitutions?
    Return $v$ unmodified
  \item Have non-empty list $[\dots/\dots]$ of substitutions?
    Return explicit substitution $v[\dots/\dots]$, or fail.
    \textbf{Should this be done after uniform subs checking?}
\end{enumerate}

\begin{code}
type PossLVSub = Either LVarSub [LVarSub]
lvlvlSubstitute :: (MonadFail m, Alternative m)
                => SubContext -> Term
               -> [LVarSub] -> m Term
lvlvlSubstitute sctxt vrt@(Var tk v@(Vbl i  vc vw)) lvlvl
  = case lvlvlSubstScan sctxt tk v [] lvlvl of
      Left (tlv, rlv@(LVbl (Vbl r_ _  rw) _ _))  
                ->  pure $ jVar tk (Vbl i vc rw)
      Right []  ->  return vrt
      Right _   -> fail "scan inconclusive"


lvlvlSubstScan sctxt tk v poss [] = Right poss
lvlvlSubstScan sctxt tk v poss (lvlv:lvlvl)
  = case lvlvSubstitute sctxt tk v lvlv of
      Right []   ->  lvlvlSubstScan sctxt tk v    poss  lvlvl
      Right [p]  ->  lvlvlSubstScan sctxt tk v (p:poss) lvlvl
      left       ->  left
\end{code}

Given $v[\ell^R/\ell^T]$ we ask the following questions:
\begin{enumerate}
  \item Is $v$ definitely in $\ell^T$?  
        If so, report this substitution as the one: 
        ($\h{Left}~(\ell^T,\ell^R)$).
  \item Is $v$ definitely not in $\ell^T$ ?
        If so, report this as not applicable: 
        ($\h{Right}~\seqof{}$).
  \item Otherwise, $v$ might be in $\ell^T$,
        so report it as possible:
        ($\h{Right}~\seqof{(\ell^T,\ell^R)}$).
\end{enumerate}

First we look at cases that definitely rule the substitution out.
\begin{code}
lvlvSubstitute :: SubContext -> Type -> Variable -> LVarSub -> PossLVSub
lvlvSubstitute sctx@(SubCtxt sc vdata) tk v@(Vbl i  vc vw) 
                  lvlv@( tlv@(LVbl tv@(Vbl ti _  tw) tis _) 
                       , rlv@(LVbl rv@(Vbl ri _  rw) ris _) )
  | vw /= tw  = Right [] -- v,tv dynamicity differs, both being dynamic
  | ti /= ri  = Right [] -- ti,ri differ
  | i `elem` tis || i `elem` ris  =  Right [] -- v removed
  | otherwise
    =  case (StdVar v) `mentionedBy` fst sc of
          Nothing  ->  Right [lvlv] -- v not mentioned 
          Just ( (VSC gv' vsD uvsC uvsCd), Nothing ) -- gv==StdVar v
            | gtlv `S.member` vsD  ||  gtlv `S.member` vsDX
                ->  Right [lvlv] -- tlv mentioned in disjoint-set
            | not ( ( gtlv `umbr` uvsC) && (gtlv `umbr` uvsCd) )
                ->  Right [lvlv] -- tlv not mentioned in coverage
            | not ( ( gtlv `umbr` uvsCX) && (gtlv `umbr` uvsCdX) )
                ->  Right [] -- tlv not mentioned in expanded coverage
            | otherwise  ->  Left lvlv 
            where
              vsDX    =  mapVToverVarSet vdata vsD 
              uvsCX   =  umap (mapVToverVarSet vdata) uvsC
              uvsCdX  =  umap (mapVToverVarSet vdata) uvsCd
          Just ( (VSC gv' _ _ (Listed vsCd)), Just vw' ) -- gv~~StdVar v 
            | not ( setGVarWhen vw' gtlv `umbr` Listed vsCd ) 
                -> Right [lvlv] -- tlv not mentioned in dyn. s.c.
            | not ( setGVarWhen vw' gtlv `umbr` Listed vsCdX ) 
                -> Right [lvlv] -- tlv not mentioned in expanded dyn. s.c.
            | otherwise  ->  Left lvlv
            where
              vsCdX  =  mapVToverVarSet vdata vsCd
          _  ->  Right [lvlv] -- this shouldn't happen 
  where
    diffdynamic = isDynamic vw && vw /= tw
    gtlv = LstVar tlv 
\end{code}


\newpage
\subsubsection{Does a uniform substitution cover the standard variable?}

The last thing we try is to see if we have a uniform substitution.
This means that:
(i) the target variables all have the same temporality;
(ii) they ``cover'' a complete list variable;
(iii) the replacements all have the same temporality;
(iv) they  ``cover'' a complete list variable.
For example:
$$[e,f,\lst O\less{x,y}/x_1,y_1,\lst O_1\less{x,y}]$$
Here the targets cover $\lst O_1$ while the replacements cover $\lst O$.

Here we only look for simple patterns such as above.
Basically we look for one or more var-term entries,
with terms that are variable terms,
and one listvar entry, where the removed variables are precisely
the target variables on the var-term list.
We also have that all target variables have the same temporality $t$,
and the replacement all have the same temporality $d$:
$$
   \seqof{(x_t,tv1_d),(y_t,tv2_d),(z_t,tv3_d)}
   \quad
   \seqof{(\lst\ell_t\less{x,y,z},\lst\rho_d\less{x,y,z})}
$$
However,
we do have a variable ($v_t$) being substituted.
$$
  v_t[tv1_d,tv2_d,tv3_d,\lst\rho_d\less{x,y,z}/x_t,y_t,z_t,\lst\ell_t\less{x,y,z}] 
  =  
  v_t[tv1_d,tv2_d,tv3_d/x_d,y_d,z_d]
$$
which can be simplifed further if $v_r$ is an observable,
to either one of the $tvN_r$ if $v_r$ is one of $x_r$, $y_r$, $z_r$,
or just $v_r$ (fail) if not.
\textbf{
  NOTE: if $\lst\ell_t$ is ``known'', and $v_t \notin \setof{x_t,y_t,z_t}$,
  then its replacement may be available.
}

The first thing we do is check that the temporality of $v$ matches that
of the first target variable. 
If not, there is no uniform substitution that can work here,
and there is only one target variable, then we can simply return $v$,
otherwise we fail.
\begin{code}
uniformSubstitute :: MonadFail m
                  => SubContext -> Term -- (Var tk v) 
                  -> [(Variable,Term)] -> [(ListVar,ListVar)]
                  -> m Term
uniformSubstitute sctx@(SubCtxt sc vdata) vrt@(Var tk v)  
                      vtl@((u,_):_) 
                      [ ( tlv@(LVbl (Vbl tid _ _) tis [])
                        , rlv@(LVbl (Vbl rid _ _) ris []) ) ]
  | tid /= rid              = usfail "different id in list-vars"
  | varWhen v /= varWhen u  = if length vtl == 1 
                              then return vrt 
                              else usfail "uniformity is inapplicable"
  | length tvws /= 1        =  usfail "vars not uniform"
  | tvw /= tlvw             =  usfail "targets not uniform"
  | length ttws /= 1        =  usfail "terms not uniform"
  | ttw /= rlvw             =  usfail "replacements not uniform"
  | otherwise               =  doUnifSub ttw tk v vtl 
  where
    usfail msg = fail ("uniformSubstitute: "++msg)
    tvws = nub $ map (varWhen . fst) vtl
    tvw = head tvws
    tlvw = lvarWhen tlv
    ttws = nub $ concat 
                $ map ( (map gvarWhen) . S.toList . fst .
                                      freeVars sc . snd ) 
                      vtl
    ttw = head $ ttws
    rlvw = lvarWhen rlv
uniformSubstitute _ _ _ _ = fail "not uniform or not supported"

doUnifSub rw tk v vtl  
  = return $ Sub tk (jVar tk $ setVarWhen rw v) 
                  $ jSubstn (mapfst (setVarWhen rw) vtl) []
-- we'll do the simplification for observables later
\end{code}


\subsubsection{Side-condition Simplification}


\textbf{NOTE: not currently used anywhere!!!!!}
Here we use side-condition information to simplify substitutions.
We drill down to the atomic side-condition, 
if any, 
that mentions the term-variable.
\begin{code}
sctxSimplify :: SubContext -> Term -> Term
sctxSimplify sctx (Sub tk vrt@(Var _ v) sub)  -- P[../..]
  = Sub tk vrt $ scSimplify (subSC sctx) (StdVar v) sub
sctxSimplify _ tm = tm

scSimplify :: SideCond -> GenVar -> Substn -> Substn
scSimplify sc gv sub 
  = case findGenVarInSC gv sc of
      Nothing   ->  sub
      Just vsc  ->  vscSimplify vsc gv sub
\end{code}

We have the following situation $P[T/V$] 
and we want to know if $V$ can occur in $P$.
We have a side-condition relating $P$ to $S$,
so we need ask if $V$ is in $S$ or not.
If $V \notin P$ then we can remove it from the substition.
We get the following combinations:
$$
\begin{array}{|c|c|c|}
\hline
   P \disj S & V \in S & V \notin P
\\\hline
   P \disj S & V \notin S & ?
\\\hline
   P \subseteq S & V \in S & ?
\\\hline
   P \subseteq S & V \notin S & V \notin P
\\\hline
\end{array}
$$
We have to check this for all $T/V$ pairs in the substitution.
\begin{code}
vscSimplify :: VarSideConds -> GenVar -> Substn -> Substn
vscSimplify (VSC _ vsD mvsC mvsCd) gv sub  
  =  mSimp mvsCd $ mSimp mvsC $ targetsCheck not vsD sub
  where 
    mSimp Everything sub    =  sub
    mSimp (Listed vs) sub  =  targetsCheck id  vs sub

targetsCheck :: (Bool -> Bool) -> VarSet -> Substn -> Substn
targetsCheck keep vs (Substn ts lvs)
  = let tl'  = filter (varTargetsCheck  keep vs) $ S.toList ts
        lvl' = filter (lvarTargetsCheck keep vs) $ S.toList lvs
    in jSubstn tl' lvl'

varTargetsCheck keep vs (tv,_) = keep $ (StdVar tv `S.member` vs)
-- we should also check if tv can be in list-vars in vs
-- this would mean keeping the top-level SC around to check such membership
-- to be implemented if required

lvarTargetsCheck keep vs (tlv,_) = keep $ (LstVar tlv `S.member` vs)
-- see comments above
\end{code}

\subsubsection{Variable/List-Variable Scope Analysis}

To apply the follow substitution definitions:
\begin{eqnarray*}
   \vv v_b
   &\cond{~\exists i \bullet \vv v_a \subseteq \lst x_{a,i}~}&
   \vv v_a \ss {} {\lst x_a^n} {\lst x_b^n}
\\ \vv P
   &\cond{~P \disj \cup_i\seqof{x^m,\lst x^n}~}&
   \vv P \ss {} {x^m;\lst x^n} {y^m;\lst y^n}
\\ \vv e_b
   &\cond{~\exists i \bullet \vv e_a \subseteq \lst x_{a,i}~}&
   \vv e_a \ss {} {\lst x_a^n} {\lst x_b^n}
\end{eqnarray*}
we need to be able to check if $\vv v_a \subseteq \lst x_a$,
or $P \disj \cup_i\seqof{x^m,\lst x^n}$.
We can only achieve this by using side-condition information.

\subsubsection{Effective Substitution}

When bindings are involved we need to compute an \emph{effective substitution}.
Given $(\bb n {x^+} t) \ss {} {v^n} {t^n}$,
we remove substitution pairs where the target variable $v_i \in x^+$,
to give the effective substitution $[t^k/v^k]$.
\begin{code}
computeEffSubst :: VarSet -> Substn -> Substn
computeEffSubst vs (Substn ts lvs) 
  = let tl' =  (S.toList ts) `stdless` vs
        lvl' = (S.toList lvs) `lstless` vs
    in jSubstn tl' lvl'
  where
    tl `stdless` vs = filter (vNotin vs) tl
    lvl `lstless` vs = filter (lvNotin vs) lvl
    vNotin vs (v,_) =  not (StdVar v `S.member` vs)
    lvNotin vs (lv,_) =  not (LstVar lv `S.member` vs)
\end{code}

\newpage
\subsubsection{Capture Avoidance}

Capture avoidance produces a substitution of variables for variables,
so that bound variables can be $\alpha$-renamed so they are not 
affected by a substitution. This is done by changing the uniqueness number
of the relevant variable.
\begin{code}
captureAvoidance :: MonadFail m 
                 => SideCond -> VarSet -> Term -> Substn -> m Substn
captureAvoidance sc vs tm sub
  = do let tfv = freeVars sc tm
       let (tgtvs,rplvs) = substRelFree sc tfv sub
       let needsRenaming = S.toList (tgtvs `S.intersection` vs)
       let knownVars = theFreeVars ( tfv `mrgFreeVars` rplvs )
       mkFresh knownVars [] [] needsRenaming

mkFresh :: (Monad m, MonadFail m)
        => VarSet
        -> [(Variable,Term)]
        -> [(ListVar,ListVar)]
        -> VarList -> m Substn
mkFresh _ sctx lvlvs [] = substn sctx lvlvs

mkFresh knVars sctx lvlvs (StdVar v : needsRenm)
  =  mkFresh knVars ((v,varAsTerm $ freshV knVars 2 v):sctx) lvlvs needsRenm

mkFresh knVars sctx lvlvs (LstVar lv : needsRenm)
  =  mkFresh knVars sctx          ((lv,freshLV knVars 2 lv):lvlvs) needsRenm

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

\subsubsection{Quantifier Body Substitution}


Used for quantifier substitution.
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
  = case lvlookup lv alvl of -- what if lv has non-null is/js components??
      Nothing   ->  gv
      -- again, we need to deal with "coverage" cases
      Just flv  ->  LstVar flv
\end{code}

\subsubsection{List-variable substitution}


Used for \texttt{Iter} substitution.
\begin{code}
listVarSubstitute :: SubContext -> [(ListVar,ListVar)] -> ListVar -> ListVar
listVarSubstitute sctxt lvlvl lv
  = case lvlookup lv lvlvl of
      Nothing   ->  lv
      Just lv'  ->  lv'
\end{code}

We want a list-variable lookup that does flexible handling
of the  ``less'' components,
with post processing of the returned value.
$$
  lookup~\lst\ell\less{L}
  ~in~
  \seqof{\dots,(\lst t\less{T},\lst r\less{R}),\dots}
$$
What relations should we expect between $\ell$, $t$ and $r$,
and $T$ and $R$?
What should be true about $L$ and $T$ for the lookup to succeed?
How should both $b$ and $B$ in final replacement $\lst b\less{B}$
be related to $\ell$, $L$, $b$ and $R$?

For now, we assume the following,
which matches most (all?) expected use cases:

$\ell,t,r$ all have the same identifier and class;
$\ell$ and $t$ have the same temporality,
while that of $r$ differs.
$T = R$, $L \supseteq T$,
and $B = L$;
while $b$ has the same temporality as $r$.
\begin{code}
lvlookup :: MonadFail m => ListVar -> [(ListVar,ListVar)] -> m ListVar
lvlookup _ [] = fail "lvlookup: list-var not found."
lvlookup lv@(LVbl v is js) ( ((LVbl tv _ _), (LVbl rv _ _) ) : rest )
    -- we should check that assumptions above hold!
  | v == tv    =  return $ LVbl rv is js
  | otherwise  =  lvlookup lv rest
\end{code}

\newpage
\section{Substitution Tests}

Assuming that $O \supseteq f$:
\begin{eqnarray*}
   (\dots P \dots)[e/x] &=& (\dots P[e/x] \dots)
\\ f[O_1/O]  &=& f_1
\\ f'[O_1/O']  &=& f_1
\\ f_1[O/O_1]  &=& f
\\ f_1[O'/O_1]  &=& f'
\\ (x'=f \land O'\less x=O\less x)[O_1/O] 
   &=& 
   (x'=f_1 \land O'\less x=O_1\less x)
\\  &\neq& (x'=f_1[/] \land O'\less x=O_1\less x)
\end{eqnarray*}
With: $O \supseteq e,f$:
\begin{eqnarray*}
   e[O_1/O'] &=& e
\\ f_1[~e,O\less x~/~x_1,O_1\!\less x~] 
   &=& 
   f[e/x] 
\end{eqnarray*}
Also
\begin{eqnarray*}
   P_d
    [ e_e,f_e,z_e,\dots,\lst u_e,\dots
    /
    x_d,y_d,z_d,\dots,\lst u_d,\dots
    ]
  &=&
   P_e[e_e,f_e/x_e,y_e]
\\ P_d
    [ e_a,f_e,z_e,\dots,\lst u_e,\dots
    /
    x_d,y_d,z_d,\dots,\lst u_c,\dots
    ]
  &=&
   P_d
    [ e_a,f_e,z_e,\dots,\lst u_e,\dots
    /
    x_d,y_d,z_d,\dots,\lst u_c,\dots
    ]
\end{eqnarray*}

Useful test bits:
\begin{code}
subC ctxt sub tm = fromJust $ substitute ctxt sub tm
sub0 = subC subContext0
\end{code}

\subsection{Non Obs. Var. Deep Substitution}

\begin{eqnarray*}
   (\dots P \dots)[e/x] &=& (\dots P[e/x] \dots)
\end{eqnarray*}
\begin{code}
iP = jId "P" ; vP = PreCond iP ; p = jpVar vP
ie = jId "e" ; ve = PreExpr ie ; e = jeVar ve
ix = jId "x" ; vx = PreVar ix  ; vx' = PostVar ix; vx1 = MidVar ix "1"
iC = jId "C" ; c t = Cons arbpred True iC [t]
e_for_x = jSubstn [(vx,e)] []
tstDeep = testCase "substitute [e/x] in (P)=(P[e/x])"
              ( sub0 e_for_x (c p) @?=  c (Sub arbpred p e_for_x) )
\end{code}

\newpage

\subsection{Expr Var Temporal Substitutions}


We should also test tempSubMiss



Assuming $O \supseteq f$ we expect:
\begin{eqnarray*}
   f[O_1/O]     &=& f_1  
\\ &\vdots&
\end{eqnarray*}
\begin{code}
jf = jId "f"
vf  = PreExpr  jf     ; f  = jeVar vf
vf' = PostExpr jf     ; f' = jeVar vf'
vf1 = MidExpr  jf "1" ; f1 = jeVar vf1

iO = jId "O" 
vO  = PreVar  iO     ; lO  = LVbl vO  [] []
vO' = PostVar iO     ; lO' = LVbl vO' [] []
vO1 = MidVar  iO "1" ; lO1 = LVbl vO1 [] []

obs_covers_f = [(LstVar lO)] `covers` StdVar vf

subObsF     = mkSubCtxt obs_covers_f []

mid_for_pre = jSubstn [] [(lO,lO1)]
mid_for_post = jSubstn [] [(lO',lO1)]
pre_for_mid = jSubstn [] [(lO1,lO)]
post_for_mid = jSubstn [] [(lO1,lO')]

esub tm sub = Sub ArbType tm sub
\end{code}
\begin{eqnarray*}
   f[O_1/O]     &=& f_1  
\\ f'[O_1/O']   &=& f_1
\\ f_1[O/O_1]   &=& f
\\ f_1[O'/O_1]  &=& f'
\end{eqnarray*}
\begin{code}
tstExprObsSubs 
  = testGroup "Expression temporality substitutions"
      [ testCase "f[O1/O] = f1" 
        ( subC subObsF mid_for_pre f @?=  f1 )
      , testCase "f'[O1/O'] = f1" 
        ( subC subObsF mid_for_post f' @?=  f1 )
      , testCase "f1[O/O1] = f" 
        ( subC subObsF pre_for_mid f1 @?=  f )
      , testCase "f1[O'/O1] = f'" 
        ( subC subObsF post_for_mid f1 @?= f' )
      ]
\end{code}

\newpage

\subsection{Same Assignment Substitution}




Given $O \supseteq e,f$:
\begin{eqnarray*}
   e[O_1/O'] &=& e
\\ f_1[~e,O\less x~/~x_1,O_1\!\less x~] 
   &=& 
   f[e/x] 
\end{eqnarray*}
\begin{code}
obs_covers_e  = [(LstVar lO)] `covers` StdVar ve
obs_covers_ef = obs_covers_e .: obs_covers_f
subObsE   = mkSubCtxt obs_covers_e []
subObsEF  = mkSubCtxt obs_covers_ef []


oless o is  = o `less` (is,[])

olessx  = oless lO  [ix]
olessx' = oless lO' [ix]
olessx1 = oless lO1 [ix]
sa_sub = jSubstn [(vx1,e)] [(olessx1,olessx)]

iy = jId "y" ; vy = PreVar iy ; vy' = PostVar iy; vy1 = MidVar iy "1"
iz = jId "z" ; vz = PreVar iz ; vz' = PostVar iz; vz1 = MidVar iz "1"




tstSameAssignSubs 
  = testGroup "Same Assignment Substitution" 
      [ testCase "e[O1/O'] = e" 
          ( subC subObsE mid_for_post e @?= e )
      , testCase "[ e,O\\x / x1,O1\\x ] is uniform+complete" 
          (isCompleteSubst sa_sub  @?= Just (During "1") )
      , testCase "f1[ e,O\\x / x1,O1\\x ] = f[e/x]" 
          (subC subObsEF sa_sub f1 @?= Sub ArbType f e_for_x)
      ]      
\end{code}

\newpage

\subsection{Assignment Proof Temporal substitution}

Assuming $O \supseteq f$ we expect:
\begin{eqnarray*}
   (x'=f \land O'\less x=O\less x)[O_1/O] 
   &=& 
   (x'=f_1 \land O'\less x=O_1\less x)
\\  &\neq& (x'=f_1[/] \land O'\less x=O_1\less x)
\end{eqnarray*}

\subsection{CTC examples}

\begin{eqnarray*}
   P_d
    [ e_e,f_e,z_e,\dots,\lst u_e,\dots
    /
    x_d,y_d,z_d,\dots,\lst u_d,\dots
    ]
  &=&
   P_e[e_e,f_e/x_e,y_e]
\\ P_d
    [ e_a,f_e,z_e,\dots,\lst u_e,\dots
    /
    x_d,y_d,z_d,\dots,\lst u_c,\dots
    ]
  &=&
   P_d
    [ e_a,f_e,z_e,\dots,\lst u_e,\dots
    /
    x_d,y_d,z_d,\dots,\lst u_c,\dots
    ]
\end{eqnarray*}

\subsection{Gathering Tests}


\begin{code}
substTests  =  testGroup "Substitution"
 [ tstDeep
 , tstExprObsSubs
 , tstSameAssignSubs
 ]
\end{code}


\newpage
\section{Substitution Composition}

Not as obvious as it looks.
\begin{eqnarray*}
   E &\defs& K + V + E \times E
\\ \sigma &:& V \pfun E
\\ \inv\sigma &\defs& v \in \sigma \implies \sigma(v)\neq v
\\ \_.\_ &:& E \times (V \pfun E) \fun E
\\ k.\sigma &\defs& k
\\ v.\sigma &\defs& \ifte {v \in \sigma} {\sigma(v)} v
\\ (e_1,e_2).\sigma &\defs& (e_1.\sigma,e_2.\sigma)
\end{eqnarray*}
The big question is:
$
\forall e,\sigma_1,\sigma_2 \bullet
\exists \sigma \bullet 
e.\sigma = (e.\sigma_1).\sigma_2
$ ?

We introduce some notation.  

If $U = \setof{u_1,\dots,u_n}$ is a set of variables, 
then $[U/U]$ is the identity substitution $[u_1,\dots,u_n/u_1,\dots,u_n]$.

Also, $[e_1,\dots,e_m,U/v_1,\dots,v_m,U]$ is short for 
$[e_1,\dots,e_m,u_1,\dots,u_n/v_1,\dots,v_m,u_1,\dots,u_n]$.

We now consider the following double substitution:
$(e[f_1,\dots,f_m/x_1,\dots,x_m])[g_1,\dots,g_n/y_1,\dots,y_n]$.
Note that there is no restriction on the relationship between the two sets
$\setof{x_1,\dots,x_m}$ and $\setof{y_1,\dots,y_n}$. 
They can be disjoint, or overlap in some way.

The following obvious shorthand suggests itself: $(e[F/X])[G/Y]$,
and we let $U = X \cup Y$, and $Z = X \cap Y$.

We partition $X$ into $X'=X\setminus Z$ and $Z$,
and let $F'$ be the replacements in $F$ for $X'$, 
and $F_Z$ the replacements for $Z$.
We treat $Y$ and  $G$ similarly to get $Y'$, $Y_Z$, $G'$ and $G_Z$.
$$
  (e[F',F_Z/X',Z])[G',G_Z/Y',Z] 
$$
Now consider a variable $v \in U$.
\begin{eqnarray*}
   v \notin X \land v \notin Y 
   &\implies& (v[F',F_Z/X',Z])[G',G_Z/Y',Z] = v
\\ v \notin X \land v   \in  Y 
   &\implies& (v[F',F_Z/X',Z])[G',G_Z/Y',Z] = G' 
   \quad \textbf{as } v \in Y'
\\ v   \in  X \land v \notin Y 
   &\implies& (v[F',F_Z/X',Z])[G',G_Z/Y',Z] = F'[G',G_Z/Y',Z] 
   \quad \textbf{as } v \in X'
\\ v   \in  X \land v   \in  Y 
   &\implies& (v[F',F_Z/X',Z])[G',G_Z/Y',Z] = F_Z[G',G_Z/Y',Z] 
   \quad \textbf{as } v \in Z
\end{eqnarray*}
This suggests the following:
$$
 e[F'[G',G_Z/Y',Z],G',F_Z[G',G_Z/Y',Z]/X',Y',Z]
$$
And we can merge $X'$ and $Z$ as $X$ and $F'$ and $F_Z$ as $F$ to get:
$$
 e[F[G',G_Z/Y',Z],G'/X,Y']
$$
Similarly for $Y$ and $G$ in the $F$ substitution:
$$
 e[F[G/Y],G'/X,Y']
$$
Theorem: given $Y'= Y \setminus X$ and $G'$ as the corresponding part of $G$,
we have:
$$
 (e[F/X])[G/Y]  =  e[F[G/Y],G'/X,Y'] 
$$
Proof, stuctural induction on $E = K + V + E \times E$.
Trickiest part is the variable case which has a 4-way case split.

\newpage

Specification of substitution composition:
$$
 (e[F/X])[G/Y]  =  e[F[G/Y],G'/X,Y'] 
$$
where $[G'/Y']$ is $[G/Y]$ restricted to elements of $Y$ not in $X$.

Note that side-conditions play no role here. 
Such considerations should be applied 
after \texttt{substComp} has (fully) returned.
\begin{code}
substComp :: MonadFail m
          => Substn  -- 1st substitution performed
          -> Substn  -- 2nd substitution performed
          -> m Substn
substComp (Substn ts1 lvs1) sub2@(Substn ts2 lvs2)
  = let 
      -- compute G',Y'
      tl1 = S.toList ts1
      vl1 = map fst tl1
      tl2 = S.toList ts2
      tl2'  = filter (notTargetedIn vl1) tl2 -- G'/Y' for var-terms
      lvl1 = S.toList lvs1
      lv1 = map fst lvl1
      lvl2 = S.toList lvs2
      lvl2'  = filter (notTargetedIn lv1) lvl2 -- G'/Y' for list-vars
      -- compute  F[G/Y]
      tl1'  = mapsnd (applySub sub2) tl1
      lvl1' = mapsnd (applyLSub tl2 lvl2) lvl1
      -- compute  [ F[G/Y],G'  /  X,Y' ]
    in substn (tl1'++tl2') (lvl1'++lvl2')

notTargetedIn :: Eq t => [t] -> (t,r) -> Bool
notTargetedIn ts (t,_) = not (t `elem` ts)

applySub ::  Substn -> Term -> Term
applySub sub t  
  =  case substitute subContext0 sub t of
       Nothing  ->  Sub (termtype t) t sub
       Just t'  ->  t

applyLSub :: [(Variable,Term)] -> [(ListVar,ListVar)] 
          -> ListVar -> ListVar
applyLSub ts lvs lv
  -- ignore var-term subst for now
  = case alookup lv lvs of
      Nothing   ->  lv
      Just lv'  ->  lv'
\end{code}


\newpage

\section{Exported Test Group}

\subsection{Test Components}

A collection of standard variables:
\begin{code}
w = StaticVar $ jId "w" -- in 1st sub
x = StaticVar $ jId "x" -- in both subs
y = StaticVar $ jId "y" -- in 2nd sub
z = StaticVar $ jId "z" -- not in any sub
\end{code}
A collection of standard variable terms:
\begin{code}
tw = fromJust $ eVar ArbType w
tx = fromJust $ eVar ArbType x
ty = fromJust $ eVar ArbType y
tz = fromJust $ eVar ArbType z
\end{code}
Making 1st and 2nd substitutions:
\begin{code}
sub1 t1 t2 = jSubstn [(w,t1),(x,t2)] []
sub2 t3 t4 = jSubstn [(x,t3),(y,t4)] []
\end{code}
A default sub-context:
\begin{code}
subctxt0 = SubCtxt scTrue []
dosub tm sub = fromJust $ substitute subctxt0 sub tm
subcomp sub1 sub2 = fromJust $ substComp sub1 sub2
\end{code}
A collection of standard constants:
\begin{code}
k1 = Val ArbType $ Integer 1 
k2 = Val ArbType $ Integer 2
k3 = Val ArbType $ Integer 3
k4 = Val ArbType $ Integer 4
\end{code}
Some substitutions:
\begin{code}
s12wx = sub1 k1 k2
s34xy = sub2 k3 k4
\end{code}


\subsection{Substitution Composition}

Most of the tests are of the form: 
 $(e\sigma_1)\sigma_2 = e(\sigma_1;\sigma_2)$
where $e$ can be constant, variable or composite.
\begin{code}
subCompTest what expr sub1 sub2
  = testCase what
      ( dosub (dosub expr sub1) sub2
        @?=
        dosub expr (sub1 `subcomp` sub2)
      )
\end{code}

The most important are when $e$ is a single variable $v$,

\begin{code}
varSubstCompTests  =  testGroup "substComp applied to var"
 [ subCompTest "var in no substitution" tz s12wx s34xy
 , subCompTest "var in 1st substitution" tw s12wx s34xy
 , subCompTest "var in both substitutions" tx s12wx s34xy
 , subCompTest "var in 2nd substitution" ty s12wx s34xy
 ]
\end{code}








\begin{code}
substCompTests  =  testGroup "Substitution.substComp"
 [ varSubstCompTests
 ]
\end{code}

\subsection{Gathering Tests}

\begin{code}
int_tst_Subst :: [TF.Test]
int_tst_Subst
 = [ testGroup "\nSubstitution Internal"
     [ substTests
     , substCompTests
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
\end{code}