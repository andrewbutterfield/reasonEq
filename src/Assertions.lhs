\section{Assertions}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2021

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Assertions (
  Assertion, pattern Assertion, mkAsn, unwrapASN
, pattern AssnT, assnT, pattern AssnC, assnC
, normaliseQuantifiers
-- for testing onl
, normQTerm
) where
-- import Data.Char
-- import Data.List
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities (injMap)
import Control (mapboth,mapaccum,mapsnd)
import LexBase
import Variables
import AST
import FreeVars
import SideCond

-- import Test.HUnit hiding (Assertion)
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}


\newpage
\subsection{Introduction}


An assertion is a \emph{normalised} predicate term coupled with side-conditions.
\begin{code}
newtype Assertion = ASN (Term, SideCond) deriving (Eq,Ord,Show,Read)

pattern Assertion tm sc  <-  ASN (tm, sc)
pattern AssnT tm         <-  ASN (tm, _ )
pattern AssnC sc         <-  ASN (_,  sc)
\end{code}


We make an assertion by normalising its bound variables,
and then merging nested quantifiers:
\begin{code}
mkAsn :: Term -> SideCond -> Assertion
mkAsn tm sc  = ASN $ normaliseQuantifiers tm sc
\end{code}

We can select assertion components by function,
and unwrap completely:
\begin{code}
assnT :: Assertion -> Term
assnT (ASN (tm, _))  =  tm

assnC :: Assertion -> SideCond
assnC (ASN (_, sc))  =  sc

unwrapASN :: Assertion -> (Term, SideCond)
unwrapASN (ASN tsc)  =  tsc
\end{code}


\subsubsection{Normalising Bound Variables}

We want all bound-variables to be unique in a term, so that, for example,
the term
$$
  \forall x \bullet x > y \land \exists x \bullet x = z + 42
  \qquad
  (\text{really:  }
   \forall x_0 \bullet x_0 > y_0 \land \exists x_0 \bullet x_0 = z_0 + 42)
$$
becomes:
$
  \forall x_i \bullet x_i > y_0 \land \exists x_j \bullet x_j = z_0 + 42
$
where $i > 0$, $j > 0$, and $i \neq j$.

Turns out there is a fairly simple algorithm, that doesn't require the
predicate to be zero'ed in advance!

\textbf{Note:}
\textit{
We need to be careful with non-substitutable terms!
}
\begin{eqnarray*}
   \theta,\mu : VV &\defs&  name \pfun \Nat
\\
\\ Norm &:& T \fun T
\\ Norm(p)                       &\defs& \pi_1(norm_\theta(p))
\\
\\ norm &:& VV \fun T \fun (T \times VV)
\\ norm_\mu(v)         &\defs & (v_{\mu(v)} \cond{v \in \mu} v_0,\mu)
\\ norm_\mu(e)         &\defs & (e,\mu)
\\ norm_\mu(P)         &\defs & (P,\mu)
\\ norm_\mu(p \land q) &\defs & (p' \land q',\mu'')
\\                     &\where& (p',\mu') = norm_\mu(p)
\\                     &      & (q',\mu'') = norm_{\mu'}(q)
\\ norm_\mu(\forall x \bullet p) &\defs& (\forall x_{\mu'(x)} \bullet p',\mu'')
\\                     &\where& \mu' = (\mu\override\maplet x 1)
                                       \cond{x \in \mu}
                                       (\mu\override\maplet x {\mu(x)+1})
\\                     &      & (p',\mu'') = norm_{\mu'}(p)
\end{eqnarray*}
Note that we need to thread the  map parameter $\mu$ into and out of each call
to $norm$ to ensure that we get full uniqueness of bound variable numbers.

We map bound variable names, and class and when attributes, to their unique numbers:
\begin{code}
type VarVersions = Map (String,VarClass,VarWhen) Int
\end{code}

We can also generate an explicit substitution from such a map:
\begin{code}
mkVVsubstn :: VarVersions -> Substn
mkVVsubstn vv
 = fromJust $ substn tsvv lvsvv
 where
   (tsvv,lvsvv) = unzip $ map mkvsubs $ M.assocs vv
   mkvsubs ((nm,cls,whn),u)
     = ((v0,tvu),(lv0,lvu))
     where
       v0 = Vbl (jId nm)    cls whn
       vu = Vbl (jIdU nm u) cls whn
       tvu = jVar (E ArbType) (Vbl (jIdU nm u) cls whn)
       lv0 = LVbl v0 [] []
       lvu = LVbl vu [] []
\end{code}

Quantifier normalisation:
\begin{code}
normaliseQuantifiers :: Term -> SideCond -> (Term, SideCond)
normaliseQuantifiers tm sc
  = let (tm', vv') = normQ M.empty tm
    in  (tm', normSC vv' sc)
\end{code}

\begin{code}
normQTerm :: Term -> Term
normQTerm tm = fst $ normaliseQuantifiers tm scTrue
\end{code}

\newpage

The real work is done here:
\begin{code}
normQ :: VarVersions -> Term -> (Term, VarVersions)
\end{code}

\begin{eqnarray*}
   norm_\mu(v)         &\defs & (v_{\mu(v)} \cond{v \in \mu} v_0,\mu)
\\ norm_\mu(e)         &\defs & (e,\mu)
\\ norm_\mu(P)         &\defs & (P,\mu)
\end{eqnarray*}
It is very important not to produce substitutions on term variables here.
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv (Var tk v@(Vbl (Identifier nm _) ObsV _))
                       =  ( fromJust $ var tk $ normQVar vv v, vv )
normQ vv v@(Var tk _)  =  ( v,                                 vv )
\end{code}

\begin{eqnarray*}
   norm_\mu(p \land q) &\defs & (p' \land q',\mu'')
\\                     &\where& (p',\mu') = norm_\mu(p)
\\                     &      & (q',\mu'') = norm_{\mu'}(q)
\end{eqnarray*}
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv (Cons tk sb n ts)       =  (Cons tk sb n ts',vv')
                              where (ts',vv') =  mapaccum normQ vv ts
normQ vv (Sub tk tm s)
  = let (tm',vv') = normQ vv tm
        (s',vv'') = normQSub vv' s
    in (Sub tk tm' s',vv'')

normQ vv (Iter tk sa na si ni lvs)
  =  (Iter tk sa na si ni $ map (normQLVar vv) lvs,vv)
\end{code}

\begin{eqnarray*}
   norm_\mu(\forall x \bullet p) &\defs& (\forall x_{\mu'(x)} \bullet p',\mu'')
\\                     &\where& \mu' = (\mu\override\maplet x 1)
                                       \cond{x \in \mu}
                                       (\mu\override\maplet x {\mu(x)+1})
\\                     &      & (p',\mu'') = norm_{\mu'}(p)
\end{eqnarray*}
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv (Bnd tk n vs tm)
 = let (vl',vv') = normQBound vv $ S.toList vs
       (tm',vv'') =  normQ vv' tm
   in ( fromJust $ bnd tk n (S.fromList vl') tm', vv')
normQ vv (Lam tk n vl tm)
 = let (vl',vv') = normQBound vv vl
       (tm',vv'') =  normQ vv' tm
   in ( fromJust $ lam tk n vl' tm', vv')
normQ vv (Cls n tm)
 = let (_,vv') = normQBound vv $ filter isObsGVar $ S.toList $ freeVars tm
       (tm',vv'') = normQ vv' tm
   in ( Cls n tm',vv'')
\end{code}


Anything else is unchanged
\begin{code}
--normQ :: VarVersions -> Term -> (Term, VarVersions)
normQ vv trm = (trm, vv) -- Val, Typ
\end{code}


\subsection{Normalising Side-Conditions}

Working on side-conditions is tricky,
as they mention a variable that might have have been bound more than
once before normalisation.
The only safe thing to do here is duplicate the side-condition
for each version.
This suggests the following well-formedness condition
for any (unnormalised) predicate:
any side-condition variable should either be free,
or bound precisely once.
\begin{code}
normSC :: VarVersions -> SideCond -> SideCond
normSC vv (ascs,fvs) = (map (normASC vv) ascs,normQVSet vv fvs)

normASC vv (Disjoint gv vs)  =  Disjoint (normQGVar vv gv) (normQVSet vv vs)
normASC vv (Covers gv vs)    =  Covers   (normQGVar vv gv) (normQVSet vv vs)
normASC vv (IsPre gv)        =  IsPre    (normQGVar vv gv)
\end{code}

\newpage

Functions that modify \texttt{VarVersions} \dots
\begin{code}
normQSub vv (Substn ts lvs)
  = let lvl' = mapboth (normQLVar vv) $ S.toList lvs
        (tl',vv') = normQTermSub vv $ S.toList ts
    in (fromJust $ substn tl' lvl', vv')

normQTermSub vv tl = mapaccum normQVarTerm vv tl

normQVarTerm vv (v,tm)
  = ((normQVar vv v, tm'), vv')
  where (tm',vv') = normQ vv tm

-- (vl',vv') = normQBound vv vl
normQBound vv [] = ([],vv)
normQBound vv (gv:gvs)
  = let (gv',vv') = normQBGVar vv gv
        (gvs',vv'') = normQBound vv' gvs
    in (gv':gvs', vv'')

normQBGVar vv (LstVar lv)
  =  let  (lv',vv') = normQBLVar vv lv  in  (LstVar lv', vv')
normQBGVar vv (StdVar v)
  =  let  (v', vv') = normQBVar  vv  v  in  (StdVar v',  vv')

normQBLVar vv (LVbl v is js)
  = let  (v',vv') = normQBVar vv v  in  (LVbl v' is js, vv')

normQBVar vv v@(Vbl (Identifier nm _) cls whn)
 = case M.lookup (nm,cls,whn) vv of
     Nothing  ->     ( setVarIdNumber 1 v,  M.insert (nm,cls,whn) 1  vv )
     Just u   ->  let u' = u+1
                  in ( setVarIdNumber u' v, M.insert (nm,cls,whn) u' vv )
\end{code}

Functions that lookup \texttt{VarVersions}\dots
\begin{code}
normQVSet vv vs = S.fromList $ map (normQGVar vv) $ S.toList vs

normQVList vv vl = map (normQGVar vv) vl

normQGVar vv (StdVar v)   =  StdVar $ normQVar  vv v
normQGVar vv (LstVar lv)  =  LstVar $ normQLVar vv lv

normQLVar vv (LVbl v is js) = LVbl (normQVar vv v) is js

normQVar vv v@(Vbl (Identifier nm _) cls whn)
 = setVarIdNumber (M.findWithDefault 0 (nm,cls,whn) vv) v
\end{code}
