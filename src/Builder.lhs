\section{Term Building}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Builder ( BadItemKind(..)
               , BadLength(..)
               , BuildFail(..)
               , BuildResult
               , buildTerm
               , basicCompSat
               , int_tst_Builder
               ) where
import Data.Maybe (fromJust)
--import qualified Data.Map as M

--import Utilities
import LexBase
import AST
import Syntax

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{Term Building}

Here we provide ways to build terms.
We take form specifications, a construct identifier,
and lists of terms,
check if the latter are consistent with the former.
If so we construct the correponding composite term.
If not, we look for some applicable ``exception handlers'',
and use those, otherwise we report failure.

An example is logical-and, a fully-associative binary operator,
whose form is a list of predicates of length at least two.
We can envisage three possible failures, with three exception handlers:
\begin{description}
  \item[Non-Predicate Term]
  The list contains an non-predicate term.
  If it is an expression or variable of type Boolean,
  we carry on, otherwise we fail.
  \item[Single Term]
   We return the term.
  \item[No Terms]
   We return the predicate $\True$.
\end{description}
We can also envisage some ``optimisations''.
In the case of logical-and,
we can remove any occurrences of $\True$,
and should $\False$ occur anywhere, return the whole thing as $\False$.
Such optimisations can be applied before the term builder is invoked.

These exceptions and optimisations are very much semantics-level issues,
and we need to carefully consider where they should be handled.

We start by defining strict builders,
that return either the requested term,
or an exception tailored for the specified form.

\newpage
\subsection{Building Failure Modes}

Simple form specifications are just a list of basic component kinds.
Iteration form specifications are just a basic component kind
coupled with a length constraint.
There are three possible ways for a list of terms to fail
to satisfy such specifications:
\begin{description}
  \item[Item Mismatch]
   The $i$th term does not match the $i$th, or only, specified kind.
   Here we can report the value of $i$ and the erroneous kind.
   We assume that index $i$ ranges from 1 upwards%
   \footnote{We don't program in C! We also deplore Haskell slavish copying of C in this regard!}
   .
\begin{code}
data BadItemKind = BadItemKind Int BasicComp deriving (Eq,Ord,Show,Read)
\end{code}
  \item[List Too Short]
   The list of terms supplied is too short.
   We report the length of the missing part of the list.
  \item[List Too Long]
   The list of terms is too long.
   We can report the length of the excesspart of the list.
\begin{code}
data BadLength = TooShort Int | TooLong  Int deriving (Eq,Ord,Show,Read)
\end{code}
\end{description}
It is possible to have several Item Mismatch failures,
also with one of the List Too Short/Long errors.
\begin{code}
data BuildFail
 = BuildFail [BadItemKind] (Maybe BadLength)
 deriving (Eq,Ord,Show,Read)
\end{code}
We define a build-result as either success returing a term,
or failure with a report.
\begin{code}
type BuildResult = Either BuildFail Term
nullBFail :: BuildResult
nullBFail = Left $ BuildFail [] Nothing
\end{code}

\newpage
\subsection{Building Forms}

We now provide a function that takes a form specification,
a term-kind,
an identifier, and a list of terms,
and returns the corresponding build-result:
\begin{code}
buildTerm :: FormSpec
          -> TermKind -> Identifier -> [Term]
          -> BuildResult
buildTerm (SimpleSpec (SimpleForm sf)) i ts = simpleFormTerm  sf i ts
buildTerm (IterateSpec bc lc)          i ts = iterFormTerm bc lc i ts
\end{code}

\subsubsection{Basic Component Satisfaction}

Does a term match a basic component specification?
\begin{code}
basicCompSat :: Term -> BasicComp -> Bool
basicCompSat _         AnySyn   =  True
basicCompSat (Var _ _) VarSyn   =  True
basicCompSat (Type _)  TypeSyn  =  True
basicCompSat t         ExprSyn  =  isExpr t
basicCompSat t         PredSyn  =  isPred t
basicCompSat _         _        =  False
\end{code}

\subsubsection{Building Simple Forms}

\begin{code}
simpleFormTerm :: [BasicComp]
               -> TermKind -> Identifier -> [Term]
               -> BuildResult
simpleFormTerm sf tk i ts
  =  mkSF 1 [] sf ts
  where
    mkSF _ []   [] []  =  Right $ Cons tk i ts
    mkSF _ kibs [] []  =  Left $ BuildFail (reverse kibs) Nothing
    mkSF _ kibs [] xs  =  Left $ BuildFail (reverse kibs)
                                         $ Just $ TooLong  $ length xs
    mkSF _ kibs uf []  =  Left $ BuildFail (reverse kibs)
                                         $ Just $ TooShort $ length uf
    mkSF i kibs (bc:bcs) (t:ts)
     | t `basicCompSat` bc  =  mkSF (i+1) kibs                      bcs ts
     | otherwise            =  mkSF (i+1) (BadItemKind i bc : kibs) bcs ts
\end{code}

Some tests:
\begin{code}
condForm = [PredSyn,ExprSyn,PredSyn]
i_cond = fromJust $ ident "cond"
i_P = fromJust $ ident "P" ; v_P = PredVar i_P Static
p = fromJust $ pVar v_P
i_Q = fromJust $ ident "Q" ; v_Q = PredVar i_Q Static
q = fromJust $ pVar v_Q
i_c = fromJust $ ident "c" ; v_c = PreExpr i_c
c = fromJust $ eVar ArbType v_c
mkCond ts = simpleFormTerm condForm P i_cond ts

simpleFormTermTests
 = testGroup "Builder.simpleFormTerm (P <| c |> Q)"
    [ testCase "No terms"
      ( mkCond [] @?= Left (BuildFail [] (Just (TooShort 3))) )
    , testCase "One (correct) term"
      ( mkCond [p]
        @?= Left (BuildFail [] (Just (TooShort 2))) )
    , testCase "Two (correct) terms"
      ( mkCond [p,c]
        @?= Left (BuildFail [] (Just (TooShort 1))) )
    , testCase "Three correct terms"
      ( mkCond [p,c,q] @?= Right (PCons i_cond [p,c,q]) )
    , testCase "Three terms, 1 incorrect"
      ( mkCond [p,q,p] @?= Left (BuildFail [BadItemKind 2 ExprSyn] Nothing) )
    , testCase "One (incorrect) term"
      ( mkCond [c]
        @?= Left (BuildFail [BadItemKind 1 PredSyn] (Just (TooShort 2))) )
    , testCase "Two (incorrect) terms"
      ( mkCond [c,p]
        @?= Left (BuildFail [BadItemKind 1 PredSyn,BadItemKind 2 ExprSyn]
                            (Just (TooShort 1))) )
    , testCase "Three incorrect terms"
      ( mkCond [c,p,c] @?=
        Left (BuildFail
             [BadItemKind 1 PredSyn,BadItemKind 2 ExprSyn,BadItemKind 3 PredSyn]
             Nothing) )
    , testCase "Four incorrect terms"
      ( mkCond [c,p,c,q] @?=
        Left (BuildFail
             [BadItemKind 1 PredSyn,BadItemKind 2 ExprSyn,BadItemKind 3 PredSyn]
             (Just (TooLong 1))) )
    , testCase "Four (correct) terms"
      ( mkCond [p,c,q,c] @?= Left (BuildFail [] (Just (TooLong 1))) )
    ]
\end{code}

\subsubsection{Building Iterated Forms}

\begin{code}
iterFormTerm :: BasicComp -> LengthConstraint
             -> TermKind -> Identifier -> [Term]
             -> BuildResult
iterFormTerm bc lc tk i ts = nullBFail
\end{code}

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_Builder :: [TF.Test]
int_tst_Builder
 = [ testGroup "\nBuilder Internal"
     [ simpleFormTermTests
     ]
   ]
\end{code}
