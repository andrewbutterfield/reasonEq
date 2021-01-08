\section{Lexical Base}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LexBase
 ( Identifier, readId
 , pattern Identifier
 , ident, uident, brktIdent
 , validIdent, isNameId, isSymbId
 , idName, idUName, splitClosureId
 , Token
 , pattern ArbTok, pattern IdTok
 -- test only below here
 , int_tst_LexBase
 , jId, jIdU, identi
 ) where

import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\newpage
\subsection{Lexical Base Introduction}

Here we define very basic lexical elements on which both the concrete
and abstract syntaxes will be built.
The key design issues here are to be able to easily support common UTP
idioms, while making it easy for the user to define their own notation.
For now we recognise the following kinds of tokens:
\begin{description}
  \item[Whitespace]
    longest sequence of characters satisfying \texttt{isSpace}.
  \item[Numeric]
    longest sequence of characters satisfying \texttt{isDigit}.
  \item[Symbol]
    longest sequence of characters satisfying \texttt{isSymbol}.
  \item[Identifier]
    longest sequence of characters satisfying the requirements of
    an identifier as defined in this module.
\end{description}
Anything else is `arbitrary`.

\newpage
\subsection{Identifiers}

We consider `identifiers' to either
be \emph{ASCII only}%
\footnote{
 We want theory files to be portable. Unicode is not portable.
}
strings that satisfy a fairly standard convention
for program variables, namely starting with an alpha character,
followed by zero or more alphas, and digits,
or a mix of ``symbols'', which do not include alphas.
In addition,
we don't allow most whitespace, quotes, or dots
in either form of identifier.
We do permit variable identifiers to have some decoration
characters: \verb@'_$?'@, and may start with \verb@_?".@
We do allow symbols to end with a space character%
---%
this is necessary for some long symbols.

We also associate a natural number with every identifier
that is used for normalisation and $\alpha$-renaming.
This is typically initialised to zero when an identifier is built.
\begin{code}
data Identifier = Id String Int deriving (Eq, Ord, Show, Read)

readId :: String -> Identifier
readId = read

pattern Identifier nm u <- Id nm u

decorChar = "'_$?"

isIdStartChar c  =  isAscii c && (c `elem` "_?" || isAlpha c)
isIdContChar  c  =  isAscii c && (isAlpha c || isDigit c || c `elem` decorChar)
isValidSymbol c  =  isAscii c && not(isSpace c||isAlpha c||c `elem` "_$'.`\"")

validIdent :: String -> Bool
validIdent str@(c:cs)
  =  isIdStartChar c  && all isIdContChar cs
     ||
     not (isDigit c) && all isValidSymbol (init str)
                     && ( c' == ' ' || isValidSymbol c' )
  where c' = last str
validIdent _           =  False -- no empty/null identifiers !

ident :: Monad m => String -> m Identifier
ident nm
 | validIdent nm  = return $ Id nm 0
ident nm = fail ("'"++nm++"' is not an Identifier")

uident :: Monad m => String -> Int -> m Identifier
uident nm u
 | validIdent nm  = return $ Id nm u
uident nm _ = fail ("'"++nm++"' is not an Identifier")

-- a hack for now - should check for validBracket-ness !!!
brktIdent :: Monad m => String -> String -> m Identifier
brktIdent lbr rbr = return $ Id (lbr++'_':rbr) 0

isNameId, isSymbId :: Identifier -> Bool
isNameId (Id (c:_) _)  =  isAlpha c
isSymbId (Id (c:_) _)  =  isValidSymbol c

idName :: Identifier -> String
idName (Id nm _) = nm

idUName :: Identifier -> String
idUName (Id nm u) = nm ++ show u
\end{code}

\begin{code}
splitClosureId (Id clsnm _)
  = case splitAround '_' clsnm of
      Nothing         ->  (clsnm,clsnm)
      Just (lbr,rbr)  ->  (lbr,rbr)
\end{code}

Identifier Tests:
\begin{code}
identTests
 = testGroup "LexBase.ident"
    [ testCase "ident \"\""     ( ident ""     @?=  Nothing )
    , testCase "ident \"a\""    ( ident "a"    @?=  Just (Id "a" 0) )
    , testCase "ident \"Z\""    ( ident "Z"    @?=  Just (Id "Z" 0) )
    , testCase "ident \"++\""   ( ident "++"   @?=  Just (Id "++" 0) )
    , testCase "ident \"\172\"" ( ident "\172" @?=  Nothing )
    , testCase "ident \"_\""    ( ident "_"    @?=  Just (Id "_" 0) )
    , testCase "ident \"'\""    ( ident "'"    @?=  Nothing )
    , testCase "ident \"5\""    ( ident "5"    @?=  Nothing )
    , testCase "ident \"a?\""   ( ident "a?"   @?=  Just (Id "a?" 0) )
    , testCase "ident \"Z@\""   ( ident "Z@"   @?=  Nothing )
    , testCase "ident \"_a\""   ( ident "_a"   @?=  Just (Id "_a" 0) )
    , testCase "ident \"'a\""   ( ident "'a"   @?=  Nothing )
    , testCase "ident \"5a\""   ( ident "5a"   @?=  Nothing )
    , testCase "ident \"Mp\""   ( ident "Mp"   @?=  Just (Id "Mp" 0) )
    , testCase "ident \"N5\""   ( ident "N5"   @?=  Just (Id "N5" 0) )
    , testCase "ident \"R_\""   ( ident "R_"   @?=  Just (Id "R_" 0) )
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

jId :: String -> Identifier
jId = fromJust . ident
jIdU :: String -> Int -> Identifier
jIdU nm u = fromJust $ uident nm u
identi :: String -> Int ->Identifier
identi nm i = jId (nm++show i) -- number is part of name

int_tst_LexBase :: [TF.Test]
int_tst_LexBase
 = [ testGroup "\nLexBase (INTERNAL))"
     [ identTests
     ]
   ]
\end{code}
