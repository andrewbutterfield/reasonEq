\chapter{Term Zipper}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TermZipper
 ( TermZip
 , Term'(..), TermSubL -- internals needed for focus-hilite pretty-printing (?)
 -- perhaps the relevant p.p. bits can be imported here so we do it locally?
 -- reccommended abstraction:
 , mkTZ, downTZ, upTZ, exitTZ
 , followTZ, pathTZ
 , getTZ, setTZ, setfTZ
 , int_tst_TermZip
 ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe

import Utilities
import Symbols
import LexBase
import Variables
import AST

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

import Debugger
\end{code}

\newpage
\section{Introduction}

We define types for the key concepts behind a proof,
such as the notion of assertions, proof strategies,
and proof calculations.


We implement a zipper on the publicly available patterns.
Algebraically:
\begin{eqnarray*}
   t &::=& Val_k~n
      ~|~  Iter_k~i~i~lv
      ~|~  Type~\tau
      ~|~  Var_k~v \qquad \mbox{--- no term subcomponent}
\\   &~|~& Cons_k~b~i~t^*
      ~|~  Bind_k~i~vs~t
      ~|~  Lam_k~i~vl~t
      ~|~  Cls~i~t
      ~|~  Sub_k~t~s
\\ s &::=& Substn~(v,t)^*~(v,v)^*
\\ t' &::=& Cons'_k~b~i~t^*~t^*
       ~|~  Bnd'_k~i~vs
       ~|~  Lam'_k~i~vl
       ~|~  Cls'~i
       ~|~  Sub'_k~s
       ~|~  Substn'_k~t~(v,v)^*~(v,t)^*~v~(v,t)^*
\end{eqnarray*}
\begin{code}
type TermSubL = [(Variable, Term)]

data Term'
  = Cons'   Type Subable Identifier [Term] -- terms before focus, reversed
                                        [Term] -- terms after focus
  | Bnd'    Type Identifier VarSet
  | Lam'    Type Identifier VarList
  | Cls'             Identifier
  | Sub'    Type Substn
  | Substn' Type Term LVarSubs TermSubL  -- subst-pairs before, reversed
                                  Variable -- focus target variable
                                  TermSubL  -- subst-pairs after focus
  deriving (Eq,Show,Read)


type TermZip = (Term,[Term'])
\end{code}

\newpage
We now define the basic zip maneuvers.

\section{Zip Creation}~

\begin{code}
mkTZ :: Term -> TermZip
mkTZ trm = (trm,[])
\end{code}

\section{Zip Descent}~

\begin{code}
downTZ :: Int -> TermZip -> ( Bool -- true if descent occurred, false otherwise
                            , TermZip )
downTZ n tz@(t,wayup)
  =  case descend n t of
      Nothing  ->  (False,tz) -- null op, if not possible to descend as requested
      Just (td,t')  ->  (True,(td,t':wayup))

descend n (Cons tk sb i ts)
  = case peel n ts of
      Nothing  ->  Nothing
      Just (before,nth,after)  ->  Just (nth,Cons' tk sb i before after)
descend 1 (Bnd tk i vs t)  =  Just (t,Bnd' tk i vs)
descend 1 (Lam tk i vl t)  =  Just (t,Lam' tk i vl)
descend 1 (Cls i t)        =  Just (t,Cls' i)
descend 1 (Sub tk t sub)   =  Just (t,Sub' tk sub)
descend n (Sub tk t sub)   =  sdescend tk t (n-1) sub
descend _ _                =  Nothing

sdescend tk t n (Substn tsub lvsub)
  = case peel n (S.toList tsub) of
      Nothing  ->  Nothing
      Just (before,(v,t'),after)
        -> Just (t',Substn' tk t lvsub before v after)
\end{code}

\subsection{Zip Descent by Path}

Follow a list of numbers down.
No change if any number fails to produce a descent step.
\begin{code}
followTZ :: [Int] -> TermZip -> ( Bool -- true if descent occurred.
                                , TermZip )
followTZ path tz0
  = follow tz0 False path -- boolean set true once a down step is done
  where
    follow tz stepped [] = if stepped then (True,tz) else (False,tz0)
    follow tz stepped (n:ns)
      = let (ok,tz') = downTZ n tz in
        if ok then follow tz' True ns else (False,tz0)

pathTZ :: [Int] -> Term -> TermZip
pathTZ path = snd . followTZ path . mkTZ
\end{code}


\newpage
\section{Zip Ascent}~

\begin{code}
upTZ :: TermZip -> ( Bool -- true if ascent occurred, false otherwise
                   , TermZip )
upTZ tz@(_,[]) = (False, tz) -- null op, if already at top
upTZ (t,(parent:wayup)) =  (True, (ascend t parent, wayup))

ascend :: Term -> Term' -> Term -- should always succeed
ascend t (Cons' tk sb i before after)  =  Cons tk sb i $ wrap before t after
ascend t (Bnd' tk i vs)
  | otherwise                          =  fromJust $ bnd tk i vs t
ascend t (Lam' tk i vl)                =  fromJust $ lam tk i vl t
ascend t (Cls' i)                      =  Cls i t
ascend t (Sub' tk sub)                 =  Sub tk t sub
ascend t (Substn' tk tt lvarsub before v after)  =  Sub tk tt sub
  where sub = fromJust (substn (wrap before (v,t) after) (S.toList lvarsub))

wrap before x after = reverse (x:before) ++ after
\end{code}

\section{Zip Exit}

\begin{code}
exitTZ :: TermZip -> Term
exitTZ (t,[])  =  t
exitTZ tz = exitTZ $ snd $ upTZ tz
\end{code}

\section{Zip Get and Set}
We also provide get and set functions for the zipper focus:
\begin{code}
getTZ :: TermZip -> Term
getTZ (t,_) = t

setTZ :: Term -> TermZip -> TermZip
setTZ t (_,wayup) = (t,wayup)

setfTZ :: (Term -> Term) -> TermZip -> TermZip
setfTZ f (t,wayup) = (f t, wayup)
\end{code}

\newpage
\section{Zipper Tests}

These tests involve a descent of zero or more levels,
the optional modification of the focus, and then an exit.
The outcome is then compared with an expected result.
We start with a test harness.
\begin{code}
-- general purpose
zipTest :: String  -- test description
        -> (Term -> Term)  -- function that builds an interesting term
        -> [Int] -- parameters for a descent
        -> (Term -> Term) -- function to modify focus
        -> Term -- test term
        -> Term -- expected result
        -> TF.Test
zipTest descr buildf waydown modf tt tx
 = testCase descr (inandout waydown modf (buildf tt) @?= tx)

-- works only if descent parameters are right,
-- and buildf is not a constant function
zipTest' :: String  -- test description
        -> (Term -> Term)  -- function that builds an interesting term
        -> [Int] -- parameters for a descent
        -> (Term -> Term) -- function to modify focus
        -> Term -- test term
        -> TF.Test
zipTest' descr buildf waydown modf tt
 = zipTest descr buildf waydown modf tt (buildf (modf tt))

-- for top-level terms without sub-components
zipTest'' :: String  -- test description
        -> Term  -- an un-interesting? term
        -> [Int] -- parameters for a descent
        -> (Term -> Term) -- function to modify focus
        -> TF.Test
zipTest'' descr topt waydown modf
 = zipTest descr (const topt) waydown modf topt (modf topt)

inandout waydown modf testt
 = let tz = mkTZ testt
       (tf,wayup) = dig waydown tz
   in exitTZ (modf tf,wayup)

dig [] tz = tz
dig (n:ns) tz =  dig ns $ snd $ downTZ n tz
\end{code}

Now some useful test pieces:
\begin{code}
p1 = arbpred
tZ = "Z"
int = GivenType $ fromJust $ ident tZ
kint = int
ival i = Val kint (Integer i)
i42 = ival 42
box p = Cons p1 True (fromJust $ ident "BOX") [p]
x = fromJust $ ident "x"
vx = fromJust $ var kint $ Vbl x ObsV Static
tint = Typ int
iter = Iter p1 True (fromJust $ ident "and") True (fromJust $ ident "=") []
f = fromJust $ ident "F"
g = fromJust $ ident "G"
cons0 = Cons p1 True f [i42,vx,tint,iter]
cons1 p = Cons p1 True f [p,vx,tint,iter]
cons2 p = Cons p1 True f [i42,p,tint,iter]
cons3 p = Cons p1 True f [i42,vx,p,iter]
cons4 p = Cons p1 True f [i42,vx,tint,p]
i99 = ival 99
ccons p = Cons p1 True f [i42,Cons p1 True g [tint,p,vx],iter]
bcons 0 p = box $ ccons p
bcons 1 p = Cons p1 True f [i42,box $ Cons p1 True g [tint,p,vx],iter]
bcons 2 p = Cons p1 True f [i42,Cons p1 True g [tint,box p,vx],iter]
\end{code}

\begin{code}
tstZipper :: [TF.Test]
tstZipper
 = [ testGroup "Zipper Tests"
     [ zipTest'' "42 boxed@top is BOX.42" i42 [] box
     , zipTest'' "42 boxed@1 is BOX.42" i42 [1] box
     , zipTest'' "42 boxed@2;1 is BOX.42" i42 [2,1] box
     , zipTest'' "x boxed@top is BOX.x" vx [] box
     , zipTest'' "x boxed@1 is BOX.x" vx [1] box
     , zipTest'' "x boxed@1;1 is BOX.x" vx [1,1] box
     , zipTest'' (tZ++" boxed@top is BOX.x") tint [] box
     , zipTest'' (tZ++" boxed@1 is BOX.x") tint [1] box
     , zipTest'' (tZ++" boxed@1;1 is BOX.x") tint [1,1] box
     , zipTest'' ('(':_and++" = @ []) boxed@top is BOX.("++_and++" = @ [])")
                 iter [] box
     , zipTest'' ('(':_and++" = @ []) boxed@1 is BOX.("++_and++" = @ [])")
                 iter [1] box
     , zipTest'' ('(':_and++" = @ []) boxed@2;1 is BOX.("++_and++" = @ [])")
                 iter [2,1] box
     , zipTest' "F(42,x,Z,/\\{=()}) boxed@1 is F(BOX.42,..)"
               cons1 [1] box i42
     , zipTest' "F(42,x,Z,/\\{=()}) boxed@2 is F(..,BOX.x,..)"
               cons2 [2] box vx
     , zipTest' "F(42,x,Z,/\\{=()}) boxed@3 is F(..,BOX.Z,..)"
               cons3 [3] box tint
     , zipTest' "F(42,x,Z,/\\{=()}) boxed@4 is F(..,BOX./\\{..})"
               cons4 [4] box iter
     , zipTest "F(42,G(Z,99,x),/\\) boxed@top is BOX.F(...)"
               ccons [] box i99 $ bcons 0 i99
     , zipTest "F(42,G(Z,99,x),/\\) boxed@2 is BOX.F(...)"
               ccons [2] box i99 $ bcons 1 i99
     , zipTest "F(42,G(Z,99,x),/\\) boxed@2;2 is BOX.F(...)"
               ccons [2,2] box i99 $ bcons 2 i99
     ]
   ]
\end{code}

\newpage

\section{Exported Test Group}
\begin{code}
int_tst_TermZip :: [TF.Test]
int_tst_TermZip
 = [ testGroup "\nTermZipper Internal"
      tstZipper
   ]

tstTermZip = defaultMain int_tst_TermZip
\end{code}
