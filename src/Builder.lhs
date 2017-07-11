\section{Term Building}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Builder ( int_tst_Builder
               ) where
--import Data.Maybe (fromJust)
--import qualified Data.Map as M

--import Utilities
--import LexBase
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
we can remove any occurences of $\True$,
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
\begin{code}
data BadItemKind = BadItemKind Int BasicComp deriving (Eq,Ord,Show,Read)
\end{code}
  \item[List Too Short]
   The list of terms supplied is too short.
   We can report the length of the list (or the missing part?).
  \item[List Too Long]
   The list of terms is too long.
   We can report the lenth of the list (or the overrun?).
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
newtype BuildResult t = BR (Either BuildFail t)

instance Functor BuildResult where
  fmap f (BR (Left bf))  =  BR $ Left bf
  fmap f (BR (Right x))  =  BR $ Right $ f x


\end{code}

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_Builder :: [TF.Test]
int_tst_Builder
 = [ testGroup "\nBuilder Internal"
     [ testCase "1+1=2"  (1+1 @?= 2)]
   ]
\end{code}
