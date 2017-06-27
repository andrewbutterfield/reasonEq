\section{Lexical Base}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LexBase
 ( Identifier
 , pattern Identifier, ident
 , validIdent, idName
 , Token
 , pattern IdTok
 , int_tst_LexBase
 ) where

import Data.Char
import Data.List
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{Lexical Base Introduction}

Here we define very basic lexical elements on which both the concrete
and abstracts will be built.
The key design issues here are to be able to easily support common UTP
idioms, while making it easy for the user to define their own notation.

\newpage
\subsection{Identifiers}

We consider`identifiers' to be strings that satisfy a fairly standard convention
for program variables, namely starting with an alpha character,
followed by zero or more alphas, and digits.
We don't allow underscores, dollars, primes or dots in identifiers.
\begin{code}
newtype Identifier = Id String deriving (Eq, Ord, Show, Read)
pattern Identifier nm <- Id nm

validIdent :: String -> Bool
validIdent (c:cs) =  isAlpha c && all isIdContChar cs
validIdent _      =  False

ident :: Monad m => String -> m Identifier
ident nm
 | validIdent nm  = return $ Id nm
ident nm = fail ("'"++nm++"' is not an Identifier")

isIdContChar c = isAlpha c || isDigit c

idName :: Identifier -> String
idName (Id nm) = nm
\end{code}

Identifier Tests:
\begin{code}
identTests
 = testGroup "LexBase.ident"
    [ testCase "ident \"\""   ( ident ""    @?=  Nothing )
    , testCase "ident \"a\""  ( ident "a"   @?=  Just (Id "a") )
    , testCase "ident \"Z\""  ( ident "Z"   @?=  Just (Id "Z") )
    , testCase "ident \"_\""  ( ident "_"   @?=  Nothing )
    , testCase "ident \"'\""  ( ident "'"   @?=  Nothing )
    , testCase "ident \"5\""  ( ident "5"   @?=  Nothing )
    , testCase "ident \"a?\"" ( ident "a?"  @?=  Nothing )
    , testCase "ident \"Z@\"" ( ident "Z@"  @?=  Nothing )
    , testCase "ident \"_a\"" ( ident "_a"  @?=  Nothing )
    , testCase "ident \"'a\"" ( ident "'a"  @?=  Nothing )
    , testCase "ident \"5a\"" ( ident "5a"  @?=  Nothing )
    , testCase "ident \"Mp\"" ( ident "Mp"  @?=  Just (Id "Mp") )
    , testCase "ident \"N5\"" ( ident "N5"  @?=  Just (Id "N5") )
    , testCase "ident \"R_\"" ( ident "R_"  @?=  Nothing )
    ]
\end{code}

\newpage
\subsection{Tokens}

We define a basic notion of tokens as the union of the above ``wrapped'' strings
\begin{code}
data Token
 = TI Identifier
 deriving (Eq,Ord,Show,Read)
pattern IdTok i = TI i
\end{code}

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_LexBase :: [TF.Test]
int_tst_LexBase
 = [ testGroup "\nLexBase Internal"
     [ identTests
     ]
   ]
\end{code}
