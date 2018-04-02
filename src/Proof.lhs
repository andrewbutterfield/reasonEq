\section{Proof Support}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proof
 ( Assertion
 , TheLogic(..), flattenTheEquiv
 , Justification
 , CalcStep
 , Calculation
 , LiveProof, displayProof
 , startProof
 , displayMatches
 , matchLaws
 ) where

-- import Data.Set (Set)
-- import qualified Data.Set as S
import Data.Maybe
--
import Utilities
import LexBase
-- import Variables
import AST
import SideCond
import TermZipper
import VarData
import Binding
import Matching
-- import Builder
--
import NiceSymbols
import TestRendering
--
-- import Test.HUnit hiding (Assertion)
-- import Test.Framework as TF (defaultMain, testGroup, Test)
-- import Test.Framework.Providers.HUnit (testCase)

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

\newpage
\subsection{Logic}

To make the matching work effectively,
we have to identify which constructs play the roles
of truth, logical equivalence, implication and conjunctions.
$$ \textit{true} \qquad \equiv \qquad \implies \qquad \land $$
\begin{code}
data TheLogic
  = TheLogic
     { theTrue :: Term
     , theEqv  :: Identifier
     , theImp  :: Identifier
     , theAnd  :: Identifier
     }
\end{code}
We also want to provide a way to ``condition'' predicates
to facilitate matching  and proof flexibility.
In particular, we want to ``associatively flatten'' nested
equivalences.
\begin{code}
flattenTheEquiv :: TheLogic -> Term -> Term
flattenTheEquiv theLogic t
  = fTE (theEqv theLogic) t
  where

    fTE eqv (Cons tk i ts)
      | i == eqv  = mkEqv tk eqv [] $ map (fTE eqv) ts
    fTE _ t = t

    mkEqv tk eqv st [] = Cons tk eqv $ reverse st
    mkEqv tk eqv st (t@(Cons tk' i' ts'):ts)
      | i' == eqv  =  mkEqv tk eqv (ts' `mrg` st) ts
    mkEqv tk eqv st (t:ts) = mkEqv tk eqv (t:st) ts

    []     `mrg` st  =  st
    (t:ts) `mrg` st  =  ts `mrg` (t:st)
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

The actions involed in a proof calculation step are as follows:
\begin{itemize}
  \item Select sub-term.
  \item Match against laws.
  \item Select preferred match and apply its replacement.
  \item Record step (which subterm, which law).
\end{itemize}

We want a zipper for the first three,
and a calculation-step record for the fourth.
We will prototype something simple for now.
\begin{code}
type Justification
  = ( String   -- law name
    , [Int] )  -- zipper descent arguments

type CalcStep
  = ( Justification -- step justification
    , Term )  -- previous term

type Calculation
  = ( Term -- end (or current) term
    , [ CalcStep ] )  -- calculation steps, most recent first

type Match
 = ( String -- assertion name
   , Assertion -- matched assertion
   , Binding -- resulting binding
   , Term  -- replacement
   )

type Matches
  = [ ( Int -- match number
      , Match ) ]  -- corresponding match ) ]

type LiveProof
  = ( String -- conjecture name
    , TermZip  -- current term, focussed
    , [Int] -- current zipper descent arguments
    , SideCond -- side conditions
    , Matches -- current matches
    , [CalcStep]  -- calculation steps so far.
    )

-- temporary
displayProof :: LiveProof -> String
displayProof ( nm, tz, dpath, sc, _, steps )
 = unlines
     ( ("Proof for '"++nm++"'")
     : (trTerm 0 (getTZ tz) ++ "@" ++ show dpath++"   "++trSideCond sc)
     : map shStep steps ++ ["---"])

shStep :: CalcStep -> String
shStep ( (lnm, dpath), t )
 = unlines [ " = '"++lnm++"@" ++ show dpath ++ "'"
           , "  " ++ trTerm 0 t
           ]

displayMatches :: Matches -> String
displayMatches []  =  "no Matches."
displayMatches matches = unlines $ map shMatch matches

shMatch (i, (n, (t,sc), bind, trplc))
 = unlines [ show i ++ " : "++trTerm 0 t++"  "++trSideCond sc
             ++ " " ++ ldq ++ n ++ rdq
           , trBinding bind
           , _maplet ++ trTerm 0 trplc ]
\end{code}

We need to setup a proof from a conjecture:
\begin{code}
startProof :: String -> Assertion -> LiveProof
startProof nm (t,sc) = (nm, mkTZ t, [], sc, [], [])
\end{code}

\newpage
\subsection{Assertion Matching}

Now, the code to match laws.
Bascially we run down the list of laws,
returning any matches we find.
\begin{code}
matchLaws :: TheLogic -> [VarTable] -> Term -> [(String,Assertion)] -> Matches
matchLaws logic vts t laws
  = zip [1..] (concat $ map (domatch logic vts t) laws)
\end{code}

For each law,
we check its top-level to see if it is an instance of \texttt{theEqv},
in which case we try matches against all possible variations.
\begin{code}
domatch logic vts tC (n,asn@(tP@(Cons tk i ts@(_:_:_)),sc))
  | i == theEqv logic  =  concat $ map (eqvMatch vts tC) $ listsplit ts
  where
    eqvMatch vts tC (tsP,tsR)
      -- tC :: equiv(tsP), with replacement equiv(tsR).
      = justMatch (Cons tk i tsR) vts tC (n,((Cons tk i tsP),sc))
\end{code}

Otherwise we just match against the whole law.
\begin{code}
domatch logic vts tC law
 = justMatch (theTrue logic) vts tC law

justMatch repl vts tC (n,asn@(tP,_))
 = case match vts tC tP of
     Nothing -> []
     Just bind -> [(n,asn,bind,repl)]
\end{code}
