\chapter{Substitution}
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
import Control.Applicative

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
termTemp = S.map gvarWhen . theFreeVars . freeVars
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
for a few variables in assigments,
and for all the observation variables in sequential composition.
These lead to substitions that look like:
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

We treat observational variables ($\vv v$) 
and term variables ($\vv e,\vv P$) differently.

We assume here that $P$ is static, 
while $e$, and hence $e'$, $e_1$, are dynamic
(and similarly for $f$.)
We also let $e_a$ and $e_b$ denote variables 
with different temporality
drawn from $e,e',e_0,e_1,\dots$.


\subsubsection{Obs.-Variable Term Substitution}

\begin{eqnarray*}
   \vv v \ss {} {v^n} {r^n}  
   &\defs&  
   r_i \cond{~\exists i \bullet \vv v=v_i~} \vv v 
\\ \vv v_a \ss {} {\lst x_a^n} {\lst x_b^n}
   &\defs&
   \vv v_b
   \cond{~\exists i \bullet \vv v_a \subseteq \lst x_{a,i}~}
   \vv v_a \ss {} {\lst x_a^n} {\lst x_b^n}
\end{eqnarray*}
The test for $v_d \subseteq \lst x_{d,i}$ 
is hard, generally requiring side-conditions,
so we ignore this possibility for now.
Note also that it implies that the entire substitution is temporally uniform.
\begin{code}
substitute sctx sub@(Substn ts lvs) vrt@(Var tk v@(Vbl i ObsV whn))
  = (subVarLookup sub v) <|> (pure vrt)
\end{code}

\subsubsection{Term-Variable Term Substitution}

\textbf{Notes:} typical side-conditions found are as follows:
\begin{mathpar}
 x\notin P \and y \notin e \and  fresh:O_0
 \and
 \lst x \notin P \and \lst x \notin \lst e \and \lst x \supseteq P
 \and
 O \supseteq e \and O,O' \supseteq P
\end{mathpar}
Typical substitutions in law definitions include:
\begin{mathpar}
  ~[\lst e/\lst x] \and [O_0/O] \and [O_0/O']  
  \and
  \and [e/x] \and [x/y] \and [e[f/x]/x]
\end{mathpar}
Typical substitutions in proofs include:
\begin{mathpar}
  P[x/y] \and \Skip[O_1/O] \and R[O_1/O'] \and R[O_1/O'][O'/O_1]
  \and 
  Q[O_1,O_2/O,O']
  \and
  (\exists O_2 \bullet Q[O_2/O'] \land R[O_2/O])[O_1/O]
\end{mathpar}
Some failing examples using \texttt{substitute}:
\begin{eqnarray*}
  O,O' \supseteq \Skip : \Skip[O_1/O] &\mapsto_s& \Skip, 
  \qquad \text{---should be } \Skip[O_1/O]
\\ O,O' \supseteq R : R[O_1/O']   &\mapsto_s& R, 
  \qquad \text{---should be } R[O_1/O']
\end{eqnarray*}

Remember, here $P$ is static while $e$ is dynamic.
\begin{eqnarray*}
   \vv P \ss {} {v^n} {r^n}
   &\defs&  r_i \cond{~\exists i \bullet \vv v_i=P~} \vv P \ss {} {v^n} {r^n} 
\\ \vv P \ss {} {x^m;\lst x^n} {y^m;\lst y^n}
   &\defs&
   \vv P
   \cond{~P \disj \cup_i\seqof{x^m,\lst x^n}~}
   \vv P \ss {} {x^m;\lst x^n} {y^m;\lst y^n}
\\ \vv e_a \ss {} {\lst x_a^n} {\lst x_b^n}
   &\defs&
   \vv e_b
   \cond{~\exists i \bullet \vv v_a \subseteq \lst x_{a,i}~}
   \vv e_a \ss {} {\lst x_a^n} {\lst x_b^n}
\end{eqnarray*}
\begin{code}
substitute sctx sub@(Substn ts lvs) vrt@(Var tk v)  -- v is not ObsV
  = (subVarLookup sub v) <|> (pure $ Sub tk vrt sub)
  -- we need a helper that looks at s.c.s, lvs and v
\end{code}

% There is also a special case of $P_d[\dots]$ when
% all the targets have the same temporality as each other 
% and cover all the free variables of $P_d$,
% while all the replacements also have the same temporality as each other
% (which might differ from that of the targets).
% We shall refer to this as ``complete temporal consistency'' (c.t.c).
% We might show it as:
% $$
%   P_d
%   [ e_e,f_e,z_e,\dots,\lst u_e,\dots
%   /
%     x_d,y_d,z_d,\dots,\lst u_d,\dots
%   ]
% $$
% where $x,y,z,\dots,\lst u,\dots$ covers all free variables of $P$,
% and some targets (here $z_d,\dots,\lst u_d,\dots$)
% are replaced by versions of themselves with the replacement temporality.
% This will simplify to
% $$
%   P_e[e_e,f_e/x_e,y_e]
% $$
% We refer to $[e_e,f_e/x_e,y_e]$ as the ``effective'' substitution.
% Note that the temporalities involved need not be dynamic.

% We check for disjoint variable target temporality,
% and then for c.t.c.s.

  % | tempSubMiss vrt sub   =  return vrt
  % | isObsVar v            =  return $ subsVar v ts lvs
  % | hasCoverage && isCTC  =  return $ ctcSub tk (jVar tk $ setVarWhen repw v)
  %                                   $ jSub effTSRepl effLVSRepl
  % | otherwise             =  return $ subsVar v ts lvs
  % where
  %   (hasCoverage,cover)       = checkCoverage (subTargets sub) (scSC sctx) v
  %   (isCTC,repw,effTS,effLVS) = assessCTC (varWhen v) (S.elems ts) (S.elems lvs)
  %   effTSRepl                 = map (setVTWhen repw) effTS
  %   effLVSRepl                = map (setLVLVWhen repw) effLVS
  %   ctcSub tk tm sub@(Substn sts slvs)
  %     | S.null sts && S.null slvs  =  tm
  %     | otherwise                  =  Sub tk tm sub


% \newpage

% Checking coverage, given targets $tgts$, side-condition $sc$,
% and non-observation variable $pev$:
% does $\lst v \supseteq pev$ appear uniformly in $sc$?
% If so check that $tgts$ match $\lst v$.
% \begin{code}
%     checkCoverage tgts sc pev@(Vbl _ _ vw)
%       = case findGenVar (StdVar pev) sc of
%           Just (CoveredBy Unif _ vs)
%             -> let
%                  tgtl = map (setGVarWhen vw) $ subsumeL $ S.elems tgts
%                  vl = map (setGVarWhen vw) $ subsumeL $ S.elems vs
%                in  (vl == tgtl,vl) -- too strong?
%           -- we only consider uniform coverage for now
%           _                          ->  (False,[])
% \end{code}

% Checking non-observational variable $v$ for complete temporal consistency,
% given substitution mappings.
% Not yet seen replacement:
% \begin{code}
%     assessCTC sw []            []  =  notCTC
%     assessCTC sw (vt@( Vbl ti tc tw, Var tk (Vbl ri rc rw) ):ts ) lvs
%       | sw /= tw              =  notCTC
%       | ti == ri && tc == rc  =  assessCTC' sw rw [] [] ts lvs
%       | otherwise             =  assessCTC' sw rw [vt] [] ts lvs
%     assessCTC sw ts
%                ( lvlv@( ( LVbl (Vbl ti tc tw) tis tjs
%                  ,      LVbl (Vbl ri rc rw) ris rjs) )
%                  : lvs )
%       | sw /= tw   =  notCTC
%       | ti == ri && tc == rc && tis == ris && tjs == rjs
%                    =  assessCTC' sw rw [] [] ts lvs
%       | otherwise  =  assessCTC' sw rw [] [lvlv] ts lvs
%     -- just expect replacement variables for now.
%     assessCTC _ _ _  =  notCTC
%     notCTC  =  (False,undefined,undefined,undefined)
% \end{code}

% Have seen replacement:
% \begin{code}
%     assessCTC' sw repw effTS effLVS [] []
%       =  ( True, repw
%          , map (setVTWhen repw) effTS
%          , map (setLVLVWhen repw) effLVS )
%     assessCTC' sw repw effTS effLVS
%                 ( vt@( Vbl ti tc tw, Var tk (Vbl ri rc rw) ):ts ) lvs
%       | sw /= tw              =  notCTC
%       | repw /= rw            =  notCTC
%       | ti == ri && tc == rc  =  assessCTC' sw rw effTS      effLVS  ts lvs
%       | otherwise             =  assessCTC' sw rw (vt:effTS) effLVS  ts lvs
%     assessCTC' sw repw effTS effLVS ts
%                 ( lvlv@( ( LVbl (Vbl ti tc tw) tis tjs
%                   ,      LVbl (Vbl ri rc rw) ris rjs) )
%                   : lvs )
%       | sw /= tw   =  notCTC
%       | repw /= rw            =  notCTC
%       | ti == ri && tc == rc && tis == ris && tjs == rjs
%                    =  assessCTC' sw repw effTS effLVS        ts lvs
%       | otherwise  =  assessCTC' sw repw effTS (lvlv:effLVS) ts lvs
%     -- just expect replacement variables for now.
%     assessCTC' sw repw effTS effLVS ts lvs = notCTC
% \end{code}

% \newpage
% Working through substitution pairs:
% \begin{code}
%     -- work through std-var/term substitutions
%     subsVar :: Variable -> TermSub -> LVarSub -> Term
%     subsVar v ts lvs
%       | isObsVar v  =  subsVar' v (S.toList lvs) (S.toList ts)
%       | otherwise   =  Sub tk vrt sub

%     subsVar' :: Variable -> [(ListVar,ListVar)] -> [(Variable,Term)] -> Term
%     subsVar' v lvs [] = subsLVar v lvs
%     subsVar' v lvs ((tgtv,rplt):rest)
%       | v == tgtv  =  rplt
%       | otherwise  =  subsVar' v lvs rest

%     -- work through lst-var/lst-var substitutions
%     subsLVar v []
%       | varClass v == ObsV     =  vrt
%       | isDynamic $ varWhen v  =  vrt
%       | otherwise              =  Sub tk vrt sub
%     subsLVar v ((tgtlv,rpllv):rest)
%       | varWhen v /= lvarWhen tgtlv  =  subsLVar v rest
%       | otherwise
%       = case findGenVar (StdVar v) (scSC sctx) of
%           Just (CoveredBy NonU _ vs)
%             ->  if vs == S.singleton (LstVar tgtlv)
%                    && varWhen v == lvarWhen tgtlv
%                 then v `replacedByRpl` rpllv
%                 else vrt
%           Just (CoveredBy Unif _ vs)
%             ->  if S.size vs == 1
%                    && getIdClass (LstVar tgtlv) == getIdClass (S.elemAt 0 vs)
%                    && varWhen v == lvarWhen tgtlv
%                 then v `replacedByRpl` rpllv
%                 else vrt
%           _  ->  subsLVar v rest

%     replacedByRpl v@(Vbl i vc vw) (LVbl (Vbl _ _ lvw) is js)
%       -- we need to know if v's temporality matches that of tgtlv
%       | i `elem` is  =  vrt -- not really covered!
%       | otherwise    =  jVar tk $ Vbl i vc lvw
% \end{code}

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
    = do  alpha <- captureAvoidance vs tm effsub
          let vs' = S.fromList $ quantsSubst alpha $ S.toList vs
          asub <- substComp sctx alpha effsub --- succeeds as alpha is var-only
          tm' <- substitute sctx asub tm
          bnd tk i vs' tm'
  where
    effsub = computeEffSubst vs sub
--  effsubst = computeEffSubst sctx vs sub
--  if null effsubset then return bt else ....
substitute sctx sub lt@(Lam tk i vl tm)
  | isNullSubstn effsub  =  return lt
  | otherwise 
    = do  alpha <- captureAvoidance vs tm effsub
          let vl' = quantsSubst alpha vl
          asub <- substComp sctx alpha effsub --- succeeds as alpha is var-only
          tm' <- substitute sctx asub tm
          lam tk i vl' tm'
  where
    vs = S.fromList vl
    effsub = computeEffSubst vs sub
\end{code}

\newpage
\subsection{Substitution-Term Substitution}

\subsubsection{Assigment Substitution}

Given that we use the \texttt{Sub} term to represent assignment,
we need to treat such seperately, noting that it is n.s.::
\begin{eqnarray*}
   (x:=e)[t^n/v^v] &=& (x:=e)[t^n/v^v]
\end{eqnarray*}
\begin{code}
substitute sctx sub bt@(Sub tk _ _)
  | isAssignment bt  =  return $ Sub tk bt sub
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

\subsubsection{Capture Avoidance}


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
iC = jId "C" ; c t = PCons True iC [t]
e_for_x = jSubstn [(vx,e)] []
tstDeep = testCase "substitute [e/x] in (P)=(P[e/x])"
              ( sub0 e_for_x (c p) @?=  c (PSub p e_for_x) )
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
subObsE   = mkSubCtxt obs_covers_e
subObsEF  = mkSubCtxt obs_covers_ef


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
          (subC subObsEF sa_sub f1 @?= ESub ArbType f e_for_x)
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