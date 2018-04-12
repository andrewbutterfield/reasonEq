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
 , LiveProof, dispLiveProof
 , Proof, displayProof
 , startProof
 , displayMatches
 , matchLaws
 , proofComplete, finaliseProof
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
    , [ CalcStep ] )  -- calculation steps, in proof order

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
    , Assertion -- assertion being proven
    , TermZip  -- current term, focussed
    , [Int] -- current zipper descent arguments
    , SideCond -- side conditions
    , Matches -- current matches
    , [CalcStep]  -- calculation steps so far, most recent first
    )

type Proof
  = ( String -- assertion name
    , Assertion
    , Calculation -- Simple calculational proofs for now
    )

-- temporary
dispLiveProof :: LiveProof -> String
dispLiveProof ( nm, _, tz, dpath, sc, _, steps )
 = unlines'
     ( ("Proof for '"++nm++"'")
     : (dispTermZip tz ++ "@" ++ show dpath++"   "++trSideCond sc)
     : "..."
     : map shLiveStep steps ++ ["---"])
\end{code}

The scheme for rendering terms is as follows.
\begin{eqnarray*}
   S_p(K~t_1~\dots~t_n) &\defs& AK_p(t_1,\dots,t_n)
\\ AK_p(t_1,\dots,t_n)  &\defs&
                    asmK_p(\dots S_{pdepK(1)}(t_1)\dots S_{pdefK(n)}(t_n)\dots)
\\ pdepK(i) &\defs& \textsf{rendering context of $i$th term of $K$}
\end{eqnarray*}
The functions $AK_p$ and $pdepK$ can be used here to get precedences right
when highlighting the focus.
\begin{code}
dispTermZip :: TermZip -> String
dispTermZip tz = trTerm 0 (getTZ tz)

shLiveStep :: CalcStep -> String
shLiveStep ( (lnm, dpath), t )
 = unlines' [ " = '"++lnm++"@" ++ show dpath ++ "'"
            , trTerm 0 t
            ]

displayMatches :: Matches -> String
displayMatches []  =  "no Matches."
displayMatches matches = unlines $ map shMatch matches

shMatch (i, (n, (t,sc), bind, trplc))
 = unlines [ show i ++ " : "++ ldq ++ n ++ rdq
             ++ " " ++ trTerm 0 t ++ "  " ++ trSideCond sc
             ++ " " ++ _maplet ++ " " ++ trTerm 0 trplc
           , trBinding bind ]

displayProof :: Proof -> String
displayProof (pnm,(trm,sc),(trm',steps))
 = unlines' ( (pnm ++ " : " ++ trTerm 0 trm ++ " " ++ trSideCond sc)
              : "---"
              : ( map shStep steps )
              ++ [trTerm 0 trm'] )

shStep :: CalcStep -> String
shStep ( (lnm, dpath), t )
 = unlines' [ trTerm 0 t
            , " = '"++lnm++"@" ++ show dpath ++ "'"
            ]
\end{code}

We need to setup a proof from a conjecture:
\begin{code}
startProof :: String -> Assertion -> LiveProof
startProof nm asn@(t,sc) = (nm, asn, mkTZ t, [], sc, [], [])
\end{code}

We need to determine when a live proof is complete:
\begin{code}
proofComplete :: TheLogic -> LiveProof -> Bool
proofComplete logic (_, _, tz, _, _, _, _)  =  exitTZ tz == theTrue logic
\end{code}

We need to convert a complete live proof to a proof:
\begin{code}
finaliseProof :: LiveProof -> Proof
finaliseProof( nm, asn, tz, _, _, _, steps)
  = (nm, asn, (exitTZ tz, reverse steps))
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
      -- tC :: equiv(tsP), with replacement equiv(tsR).
    eqvMatch vts tC (tsP,tsR)
      = justMatch (eqv tsR) vts tC (n,(eqv tsP,sc))
    eqv []   =  theTrue logic
    eqv [t]  =  t
    eqv ts   =  Cons tk i ts
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
