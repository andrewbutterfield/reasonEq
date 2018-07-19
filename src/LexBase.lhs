\section{Lexical Base}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LexBase
 ( Identifier, readId
 , pattern Identifier, ident
 , validIdent, isNameId, isSymbId
 , idName
 , Token
 , pattern ArbTok, pattern IdTok
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
--import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{Lexical Base Introduction}

Here we define very basic lexical elements on which both the concrete
and abstracts will be built.
The key design issues here are to be able to easily support common UTP
idioms, while making it easy for the user to define their own notation.
For now we recognise the following kinds of tokens:
\begin{description}
  \item[Whitespace]
    longest sequence of characters satisfying \texttt{isSpace}.
  \item[Numeric]
    longest sequence of characters satisfying \texttt{isDigit}.
  \item[Numeric]
    longest sequence of characters satisfying \texttt{isSymbol}.
  \item[Identifier]
    longest sequence of characters satisfying the requirements of
    an identifier as defined in this module.
\end{description}
Anything else is `arbitrary`.

\newpage
\subsection{Identifiers}

We consider `identifiers' to either
be strings that satisfy a fairly standard convention
for program variables, namely starting with an alpha character,
followed by zero or more alphas, and digits,
or a mix of ``symbols'', which do not include alphas.
In addition,
we don't allow most whitespace, quotes, underscores, dollars, primes or dots
in either form of identifier.
We do allow symbols to end with a space character%
---%
this is necessary for some long symbols.
\begin{code}
newtype Identifier = Id String deriving (Eq, Ord, Show, Read)

readId :: String -> Identifier
readId = read

pattern Identifier nm <- Id nm

isValidSymbol c  =  not(isSpace c || isAlpha c || c `elem` "_$'.`\"")

isIdContChar c = isAlpha c || isDigit c

validIdent :: String -> Bool
validIdent str@(c:cs)
  =  not (isDigit c) && all isValidSymbol (init str)
                     && ( c' == ' ' || isValidSymbol c' )
     ||   isAlpha c  && all isIdContChar cs
  where c' = last str
validIdent _           =  False -- no empty/null identifiers !

ident :: Monad m => String -> m Identifier
ident nm
 | validIdent nm  = return $ Id nm
ident nm = fail ("'"++nm++"' is not an Identifier")

isNameId, isSymbId :: Identifier -> Bool
isNameId (Id (c:_))  =  isAlpha c
isSymbId (Id (c:_))  =  isValidSymbol c

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
    , testCase "ident \"++\"" ( ident "++"   @?=  Just (Id "++") )
    , testCase "ident \"\172\"" ( ident "\172"   @?=  Just (Id "\172") )
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
 = TA String
 | TI Identifier
 deriving (Eq,Ord,Show,Read)
pattern ArbTok s = TA s
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
