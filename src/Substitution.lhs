\section{Substitution}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019-22

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

import Utilities (alookup,injMap)
import Control (mapsnd)
import LexBase
import Variables
import AST
import FreeVars
import VarData
import SideCond

import TestRendering

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\newpage

\subsection{Introduction}

We define a function that applies a substitution to a term.
We also provide functions for $\alpha$-substitution
and substitution composition.

Substitution here is not simple, because we have list variables
that can represent either arbitrary sets/lists of variables,
or very specific sets/lists of variables.
The latter can be determined from known variable data,
as well as side-conditions.
We also have the complication of variable temporality that needs to be handled.

\subsubsection{Temporal Uniformity}

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
\\ utemp &:& VW \fun \Bool
\\ utemp(W) &\defs& \#(W)=1
\\ utemp_T &:& T \fun \Bool
\\ utemp_T &\defs& utemp(temp(t))
\\ utemp_{T^*} &:& T^* \fun \Bool
\\ utemp_{T^*}(ts) &\defs& utemp(\bigcup_{t \in ts} utem_T(v))
\\ utemp_{VL} &:& V^* \fun \Bool
\\ utemp_{VL}(vs) &\defs& utemp(\bigcup_{v \in vs} when(v))
\end{eqnarray*} 

Now, consider a general substition $e[\lst r/\lst x]$


\subsubsection{Substitution Contexts}

All substitutions need a context argument that describes the following
aspects of the current state of a proof:
\begin{itemize}
  \item side-conditions
  \item dynamic \texttt{Subscript}s in scope
\end{itemize}
\begin{code}
data SubContext
  =  SCtxt  { scSC :: SideCond
            }
  deriving (Eq,Ord,Show,Read)

mkSubCtxt = SCtxt

subContext0 = mkSubCtxt scTrue
\end{code}

\newpage
\subsection{Term Substitution}

\begin{code}
substitute :: (Monad m, MonadFail m) => SubContext -> Substn -> Term -> m Term
\end{code}

\subsubsection{Var-Term Substitution}


\textbf{
  Uninterpreted Predicate/Expression variables need to have explicit substitutions.  
  So $(\dots P \dots)[e/x]$ should become $(\dots P[e/x] \dots)$.
  That is what the second line below says, but it is not happening.
}

\textbf{
  We also want $e[O_1/O] = e_1$ and $e_1[O/O_1] = e$.
}



\begin{eqnarray*}
   \vv v \ss {} {v^n} {r^n}  &\defs&  r^i \cond{\vv v=v^i} v,
                                                \mbox{ for one $i \in 1\dots n$}
\\ \vv P \ss {} {v^n} {r^n}
   &\defs&  r^i \cond{\vv P=v^i} \vv P \ss {} {v^n} {r^n},
                                                                  \mbox{ ditto.}
\\ \vv v_d \ss {} {\dots,\lst x_d,\dots} {\dots,\lst x_e,\dots}
   &\defs&
   \vv v_e
   \cond{\vv v_d \subseteq \lst x_d}
   \vv v_d \ss {} {\dots,\dots} {\dots,\dots},
   \mbox{$d,e$ are dynamic temporalities.}
\\ \vv P_d \ss {} {\dots,\lst x_d,\dots} {\dots,\lst x_e,\dots}
   &\defs&
   \vv P_e
   \cond{\vv P_d \subseteq \lst x_d}
   \vv P_d \ss {} {\dots,\dots} {\dots,\dots},
   \mbox{ ditto.}
\end{eqnarray*}
There is also a special case of $P_d[\dots]$ when
all the targets have the same temporality as each other 
and cover all the free variables of $P_d$,
while all the replacements also have the same temporality as each other
(which might differ from that of the targets).
We shall refer to this as ``complete temporal consistency'' (c.t.c).
We might show it as:
$$
  P_d
  [ e_e,f_e,z_e,\dots,\lst u_e,\dots
  /
    x_d,y_d,z_d,\dots,\lst u_d,\dots
  ]
$$
where $x,y,z,\dots,\lst u,\dots$ covers all free variables of $P$,
and some targets (here $z_d,\dots,\lst u_d,\dots$)
are replaced by versions of themselves with the replacement temporality.
This will simplify to
$$
  P_e[e_e,f_e/x_e,y_e]
$$
We refer to $[e_e,f_e/x_e,y_e]$ as the ``effective'' substitution.
Note that the temporalities involved need not be dynamic.

We check for c.t.c.s first.
\begin{code}
substitute sctx sub@(Substn ts lvs) vrt@(Var tk v)
  | isObsVar v            =  return $ subsVar v ts lvs
  | hasCoverage && isCTC  =  return $ ctcSub tk (jVar tk $ setVarWhen repw v)
                                    $ jSub effTSRepl effLVSRepl
  | otherwise             =  return $ subsVar v ts lvs
  where
    (hasCoverage,cover)       = checkCoverage (subTargets sub) (scSC sctx) v
    (isCTC,repw,effTS,effLVS) = assessCTC (varWhen v) (S.elems ts) (S.elems lvs)
    effTSRepl                 = map (setVTWhen repw) effTS
    effLVSRepl                = map (setLVLVWhen repw) effLVS
    ctcSub tk tm sub@(Substn sts slvs)
      | S.null sts && S.null slvs  =  tm
      | otherwise                  =  Sub tk tm sub
\end{code}

\newpage

Checking coverage, given targets $tgts$, side-condition $sc$,
and non-observation variable $pev$:
does $\lst v \supseteq pev$ appear uniformly in $sc$?
If so check that $tgts$ match $\lst v$.
\begin{code}
    checkCoverage tgts sc pev@(Vbl _ _ vw)
      = case findGenVar (StdVar pev) sc of
          Just (CoveredBy Unif _ vs)
            -> let
                 tgtl = map (setGVarWhen vw) $ subsumeL $ S.elems tgts
                 vl = map (setGVarWhen vw) $ subsumeL $ S.elems vs
               in  (vl == tgtl,vl) -- too strong?
          -- we only consider uniform coverage for now
          _                          ->  (False,[])
\end{code}

Checking non-observational variable $v$ for complete temporal consistency,
given substitution mappings.
Not yet seen replacement:
\begin{code}
    assessCTC sw []            []  =  notCTC
    assessCTC sw (vt@( Vbl ti tc tw, Var tk (Vbl ri rc rw) ):ts ) lvs
      | sw /= tw              =  notCTC
      | ti == ri && tc == rc  =  assessCTC' sw rw [] [] ts lvs
      | otherwise             =  assessCTC' sw rw [vt] [] ts lvs
    assessCTC sw ts
               ( lvlv@( ( LVbl (Vbl ti tc tw) tis tjs
                 ,      LVbl (Vbl ri rc rw) ris rjs) )
                 : lvs )
      | sw /= tw   =  notCTC
      | ti == ri && tc == rc && tis == ris && tjs == rjs
                   =  assessCTC' sw rw [] [] ts lvs
      | otherwise  =  assessCTC' sw rw [] [lvlv] ts lvs
    -- just expect replacement variables for now.
    assessCTC _ _ _  =  notCTC
    notCTC  =  (False,undefined,undefined,undefined)
\end{code}

Have seen replacement:
\begin{code}
    assessCTC' sw repw effTS effLVS [] []
      =  ( True, repw
         , map (setVTWhen repw) effTS
         , map (setLVLVWhen repw) effLVS )
    assessCTC' sw repw effTS effLVS
                ( vt@( Vbl ti tc tw, Var tk (Vbl ri rc rw) ):ts ) lvs
      | sw /= tw              =  notCTC
      | repw /= rw            =  notCTC
      | ti == ri && tc == rc  =  assessCTC' sw rw effTS      effLVS  ts lvs
      | otherwise             =  assessCTC' sw rw (vt:effTS) effLVS  ts lvs
    assessCTC' sw repw effTS effLVS ts
                ( lvlv@( ( LVbl (Vbl ti tc tw) tis tjs
                  ,      LVbl (Vbl ri rc rw) ris rjs) )
                  : lvs )
      | sw /= tw   =  notCTC
      | repw /= rw            =  notCTC
      | ti == ri && tc == rc && tis == ris && tjs == rjs
                   =  assessCTC' sw repw effTS effLVS        ts lvs
      | otherwise  =  assessCTC' sw repw effTS (lvlv:effLVS) ts lvs
    -- just expect replacement variables for now.
    assessCTC' sw repw effTS effLVS ts lvs = notCTC
\end{code}

\newpage
If the variable is Working through substitution pairs:
\begin{code}
    -- work through std-var/term substitutions
    subsVar :: Variable -> TermSub -> LVarSub -> Term
    subsVar v ts lvs
      | isObsVar v  =  subsVar' v (S.toList lvs) (S.toList ts)
      | otherwise   =  Sub tk vrt sub

    subsVar' :: Variable -> [(ListVar,ListVar)] -> [(Variable,Term)] -> Term
    subsVar' v lvs [] = subsLVar v lvs
    subsVar' v lvs ((tgtv,rplt):rest)
      | v == tgtv  =  rplt
      | otherwise  =  subsVar' v lvs rest

    -- work through lst-var/lst-var substitutions
    subsLVar v []
      | varClass v == ObsV     =  vrt
      | isDynamic $ varWhen v  =  vrt
      | otherwise              =  Sub tk vrt sub
    subsLVar v ((tgtlv,rpllv):rest)
      | varWhen v /= lvarWhen tgtlv  =  subsLVar v rest
      | otherwise
      = case findGenVar (StdVar v) (scSC sctx) of
          Just (CoveredBy NonU _ vs)
            ->  if vs == S.singleton (LstVar tgtlv)
                   && varWhen v == lvarWhen tgtlv
                then v `replacedByRpl` rpllv
                else vrt
          Just (CoveredBy Unif _ vs)
            ->  if S.size vs == 1
                   && getIdClass (LstVar tgtlv) == getIdClass (S.elemAt 0 vs)
                   && varWhen v == lvarWhen tgtlv
                then v `replacedByRpl` rpllv
                else vrt
          _  ->  subsLVar v rest

    replacedByRpl v@(Vbl i vc vw) (LVbl (Vbl _ _ lvw) is js)
      -- we need to know if v's temporality matches that of tgtlv
      | i `elem` is  =  vrt -- not really covered!
      | otherwise    =  jVar tk $ Vbl i vc lvw
\end{code}

\subsubsection{Cons-Term Substitution}

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

\subsubsection{Binding-Term Substitution}

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
substitute sctx sub bt@(Bnd tk i vs tm)
  = do alpha <- captureAvoidance vs tm sub
       let vs' = S.fromList $ quantsSubst alpha $ S.toList vs
       asub <- substComp sctx alpha sub --- succeeds as alpha is var-only
       tm' <- substitute sctx asub tm
       bnd tk i vs' tm'
substitute sctx sub lt@(Lam tk i vl tm)
  = do alpha <- captureAvoidance (S.fromList vl) tm sub
       let vl' = quantsSubst alpha vl
       asub <- substComp sctx alpha sub --- succeeds as alpha is var-only
       tm' <- substitute sctx asub tm
       lam tk i vl' tm'
\end{code}

\subsubsection{Substitution-Term Substitution}

\paragraph{Assigment Substitution}

Given that we use the \texttt{Sub} term to represent assignment,
we need to treat such seperately, noting that it is n.s.::
\begin{eqnarray*}
   (x:=e)[t^n/v^v] &=& (x:=e)[t^n/v^v]
\end{eqnarray*}
\begin{code}
substitute sctx sub bt@(Sub tk (PVar (PredVar (Identifier ":=" _) _)) _)
  = return $ Sub tk bt sub
\end{code}


\begin{eqnarray*}
   (\ss t {v^m} {t^m}) \ss {} {v^n} {t^n}
   &\defs&
     {t (\ss {} {v^m} {t^m};  \ss {} {v^n} {t^n})}
     \quad \text{if } \ss {} {v^m} {t^m};  \ss {} {v^n} {t^n} \text{ defined}
\end{eqnarray*}
\begin{code}
substitute sctx sub bt@(Sub tk tm s)
  = case substComp sctx s sub of
     Just sub' -> substitute sctx sub' tm
     Nothing   -> return $ Sub tk bt sub
\end{code}
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

\subsubsection{Non-Substitutable Terms}

\begin{eqnarray*}
   \kk k \ss {} {v^n} {t^n}   &\defs&  \kk k
\\ \xx n t \ss {} {v^n} {t^n} &\defs& \xx n t
\end{eqnarray*}
\begin{code}
substitute sctx sub tm = return tm
\end{code}

\newpage 

\subsubsection{Helper functions}

Capture avoidance produces a substitution of variables for variables,
so that bound variables can be $\alpha$-renamed so they are not 
affected by a substitution. This is done by changing the uniqueness number
of the relevant variable.
\begin{code}
captureAvoidance :: MonadFail m => VarSet -> Term -> Substn -> m Substn
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
\subsection{Substitution Tests}

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

\subsubsection{Non Obs. Var. Deep Substitution}

\begin{eqnarray*}
   (\dots P \dots)[e/x] &=& (\dots P[e/x] \dots)
\end{eqnarray*}
\begin{code}
iP = jId "P" ; vP = PreCond iP ; p = jpVar vP
ie = jId "e" ; ve = PreExpr ie ; e = jeVar ve
ix = jId "x" ; vx = PreVar ix
iC = jId "C" ; c t = PCons True iC [t]
e_for_x = jSubstn [(vx,e)] []
tstDeep = testCase "substitute [e/x] in (P)=(P[e/x])"
              ( sub0 e_for_x (c p) @?=  c (PSub p e_for_x) )
\end{code}

\newpage

\subsubsection{Expr Var Temporal Substitutions}

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

subObsF     = mkSubCtxt obs_covers_f 

mid_for_pre = jSubstn [] [(lO,lO1)]
mid_for_post = jSubstn [] [(lO',lO1)]
pre_for_mid = jSubstn [] [(lO1,lO)]
post_for_mid = jSubstn [] [(lO1,lO')]

esub tm sub = ESub ArbType tm sub
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

\subsubsection{Same Assignment Substitution}

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
subObsE   = mkSubCtxt obs_covers_e
subObsEF  = mkSubCtxt obs_covers_ef

vx1 = MidVar ix "1"
olessx  = lO  `less` ([ix],[])
olessx' = lO' `less` ([ix],[])
sa_sub = jSubstn [(vx1,e)] [(olessx',olessx)]

tstSameAssignSubs 
  = testGroup "Same Assignment Substitution" 
      [ testCase "e[O1/O'] = e" 
          ( subC subObsE mid_for_post e @?= e )
      , testCase "reaching f[e/x]" 
          (subC subObsEF sa_sub f1 @?= ESub ArbType f e_for_x)
      ]      
\end{code}

\newpage

\subsubsection{Assignment Proof Temporal substitution}

Assuming $O \supseteq f$ we expect:
\begin{eqnarray*}
   (x'=f \land O'\less x=O\less x)[O_1/O] 
   &=& 
   (x'=f_1 \land O'\less x=O_1\less x)
\\  &\neq& (x'=f_1[/] \land O'\less x=O_1\less x)
\end{eqnarray*}

\subsubsection{CTC examples}

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

\subsubsection{Gathering Tests}


\begin{code}
substTests  =  testGroup "Substitution"
 [ tstDeep
 , tstExprObsSubs
 , tstSameAssignSubs
 ]
\end{code}


\newpage
\subsection{Substitution Composition}

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
\begin{code}
substComp :: MonadFail m
          => SubContext
          -> Substn  -- 1st substitution performed
          -> Substn  -- 2nd substitution performed
          -> m Substn
substComp sctxt (Substn ts1 lvs1) sub2@(Substn ts2 lvs2)
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
      tl1'  = mapsnd (applySub sctxt sub2) tl1
      lvl1' = mapsnd (applyLSub sctxt tl2 lvl2) lvl1
      -- compute  [ F[G/Y],G'  /  X,Y' ]
    in substn (tl1'++tl2') (lvl1'++lvl2')

notTargetedIn :: Eq t => [t] -> (t,r) -> Bool
notTargetedIn ts (t,_) = not (t `elem` ts)

applySub :: SubContext -> Substn -> Term -> Term
applySub sctxt sub t  
  =  case substitute sctxt sub t of
       Nothing  ->  Sub (termkind t) t sub
       Just t'  ->  t

applyLSub :: SubContext -> [(Variable,Term)] -> [(ListVar,ListVar)] 
          -> ListVar -> ListVar
applyLSub sctxt ts lvs lv
  -- ignore var-term subst for now
  = case alookup lv lvs of
      Nothing   ->  lv
      Just lv'  ->  lv'
\end{code}


\newpage

\subsection{Exported Test Group}

\subsubsection{Test Components}

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
subctxt = SCtxt scTrue
dosub tm sub = fromJust $ substitute subctxt sub tm
subcomp sub1 sub2 = fromJust $ substComp subctxt sub1 sub2
\end{code}
A collection of standard constants:
\begin{code}
k1 = EVal ArbType $ Integer 1 
k2 = EVal ArbType $ Integer 2
k3 = EVal ArbType $ Integer 3
k4 = EVal ArbType $ Integer 4
\end{code}
Some substitutions:
\begin{code}
s12wx = sub1 k1 k2
s34xy = sub2 k3 k4
\end{code}


\subsubsection{Substitution Composition}

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

\subsubsection{Gathering Tests}

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