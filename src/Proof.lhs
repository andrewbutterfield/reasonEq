\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proof
 ( Assertion
 , Term', TermZip, mkTZ, downTZ, upTZ, exitTZ
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Binding
import Matching
import Builder

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for the key concepts behind a proof,
such as the notion of assertions, proof strategies,
and proof calculations.

\subsection{Assertions}

An assertion is simply a predicate term coupled with side-conditions.
\begin{code}
type Assertion = (Term, SideCond)
\end{code}

\subsection{Proof Calculations}

We start with the simplest proof process of all,
namely a straight calculation from a starting assertion
to a specified final assertion, usually being the axiom \textit{true}.
We need to have an AST zipper to allow sub-terms to be singled out
for match and replace,
and some way of recording what happenned,
so that proofs (complete or partial) can be saved,
restored, and reviewed.

The anatomy of a proof calculation step is as follows:
\begin{itemize}
  \item Select sub-term.
  \item Match against laws.
  \item Select preferred match and apply its replacement.
  \item Record step (which subterm, which law).
\end{itemize}

\newpage
\subsubsection{Selecting sub-terms}

We implement a zipper on the publically available patterns,
reprised here:
\begin{verbatim}
pattern Val :: TermKind -> Value -> Term
pattern Var :: TermKind -> Variable -> Term
pattern Cons :: TermKind -> Identifier -> [Term] -> Term
pattern Bind :: TermKind -> Identifier -> VarSet -> Term -> Term
pattern Lam :: TermKind -> Identifier -> VarList -> Term -> Term
pattern Sub :: TermKind -> Term -> Substn -> Term
pattern Iter :: TermKind
                -> Identifier -> Identifier -> [ListVar] -> Term
pattern Type :: Type -> Term
pattern Substn :: TermSub -> LVarSub -> Substn
type TermSub = Set (Variable, Term)
type LVarSub = Set (ListVar, ListVar)
\end{verbatim}
Algebraically:
\begin{eqnarray*}
   t &::=& Val_k~n
      ~|~  Iter_k~i~i~lv
      ~|~  Type~\tau
      ~|~  Var_k~v \qquad \mbox{--- no term subcomponent}
\\   &~|~& Cons_k~i~t^*
      ~|~  Bind_k~i~vs~t
      ~|~  Lam_k~i~vl~t
      ~|~  Sub_k~t~s
\\ s &::=& Substn~(v,t)^*~(v,v)^*
\\ t' &::=& Cons'_k~i~t^*~t^*
       ~|~  Bind'_k~i~vs
       ~|~  Lam'_k~i~vl
       ~|~  Sub'_k~s
       ~|~  Substn'_k~t~(v,v)^*~(v,t)^*~v~(v,t)^*
\end{eqnarray*}
\begin{code}
type TermSubL = [(Variable, Term)]

data Term'
  = Cons'   TermKind Identifier [Term] -- terms before focus, reversed
                                [Term] -- terms after focus
  | Bind'   TermKind Identifier VarSet
  | Lam'    TermKind Identifier VarList
  | Sub'    TermKind Substn
  | Substn' TermKind Term LVarSub TermSubL  -- subst-pairs before, reversed
                                  Variable -- focus target variable
                                  TermSubL  -- subst-pairs after focus
  deriving (Show,Read)


type TermZip = (Term,[Term'])
\end{code}

\newpage
We now define the basic zip maneuvers.

\paragraph{Zip Creation}~

\begin{code}
mkTZ :: Term -> TermZip
mkTZ trm = (trm,[])
\end{code}

\paragraph{Zip Descent}~

\begin{code}
downTZ :: Int -> TermZip -> ( Bool -- true if descent occurred, false otherwise
                            , TermZip )
downTZ n tz@(t,wayup)
  =  case descend n t of
      Nothing  ->  (False,tz) -- null op, if not possible to descend as requested
      Just (td,t')  ->  (True,(td,t':wayup))

descend n (Cons tk i ts)
  = case peel n ts of
      Nothing  ->  Nothing
      Just (before,nth,after)  ->  Just (nth,Cons' tk i before after)
descend 1 (Bind tk i vs t) = Just (t,Bind' tk i vs)
descend 1 (Lam tk i vl t) = Just (t,Lam' tk i vl)
descend 1 (Sub tk t sub) = Just (t,Sub' tk sub)
descend n (Sub tk t sub) = sdescend tk t (n-1) sub
descend _ _ = Nothing

sdescend tk t n (Substn tsub lvsub)
  = case peel n (S.toList tsub) of
      Nothing  ->  Nothing
      Just (before,(v,t'),after)
        -> Just (t',Substn' tk t lvsub before v after)

peel :: Monad m => Int -> [a] -> m ([a],a,[a])
peel n xs = ent [] n xs
 where
   ent _ _ [] = fail ""
   ent bef 1 (x:xs) = return (bef,x,xs)
   ent bef n (x:xs)
    | n < 2  =  fail ""
    | otherwise  =  ent (x:bef) (n-1) xs
\end{code}

\newpage
\paragraph{Zip Ascent}~

\begin{code}
upTZ :: TermZip -> TermZip
upTZ tz@(_,[]) = tz -- null op, if already at top
upTZ (t,(parent:wayup)) =  (ascend t parent, wayup)

ascend :: Term -> Term' -> Term -- should always succeed
ascend t (Cons' tk i before after)  =  Cons tk i $ wrap before t after
ascend t (Bind' tk i vs)            =  fromJust $ bind tk i vs t
ascend t (Lam' tk i vl)             =  fromJust $ lam tk i vl t
ascend t (Sub' tk sub)              =  Sub tk t sub
ascend t (Substn' tk tt lvarsub before v after)  =  Sub tk tt sub
  where sub = fromJust (substn (wrap before (v,t) after) (S.toList lvarsub))

wrap before x after = reverse (x:before) ++ after
\end{code}

\paragraph{Zip Exit}~

\begin{code}
exitTZ :: TermZip -> Term
exitTZ (t,[])  =  t
exitTZ tz = exitTZ $ upTZ tz
\end{code}
