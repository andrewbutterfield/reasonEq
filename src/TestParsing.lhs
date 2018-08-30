\section{Test Parsing}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TestParsing

where

import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
-- import qualified Data.Set as S
-- import Data.List (nub, sort, (\\), intercalate)
import Data.Char

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import TestRendering
\end{code}

\subsection{Test Parsing Intro.}

We provide a simple, clunky way to parse terms,
in prefix-style only.

For now we have simple literals,
composites done as prefix-functions applied to (-delimited lists of sub-terms,
and binders in standard mixfix style.

\subsection{Lexical Basics}

We have the following token classes:
\begin{description}
  \item [Numbers]~
    Just integers for now
  \item [Identifiers]~
    Identifiers as per \texttt{LexBase},
    with added decoration for variable classification
    and unicode macro expansion.
    We only expect the ``dangling space'' permitted in identifiers
    to arise as the result of macro expansion.
    \textbf{Keywords} form a subset of these.
  \item [Delimiters]~
    Small tokens used for general punctuation,
    further classified into: matched (Open/Close) bracketing; and separators.
  \item [Symbols]~
    Tokens assembled from everything else.
\end{description}

\begin{code}
data TToken
  =  TNum String
  |  TId  String
  |  TOpen  String
  |  TClose  String
  |  TSep String
  |  TSym String
  |  Terr String
  deriving (Eq,Show)
\end{code}

We shall use decoration to indicate variable temporality.
We use underscore for ``During'',
and a designated decoration character ($\delta$)
to indicate ``Before'' or ``After''.

\begin{tabular}{|l|c|l|}
\hline
  Temp. & Math. & String
\\\hline
  Static & $v$ & \texttt{v}
\\\hline
  Before & $v$ & $\delta$\texttt{v}
\\\hline
  During & $v_m$ & \texttt{v\_m}
\\\hline
  After & $v'$ & \texttt{v}$\delta$
\\\hline
\end{tabular}

We want a character that is on both Apple, Windows and ``unix'' keyboards.
\begin{code}
decorChar = '?' -- not really used for anything else!
\end{code}

We shall predefine delimiters as constant for now.
Later on these will be parameters to the whole parsing process.
\begin{code}
openings  =  "([{"
closings  =  "}])"
separators = ","  -- really don't want too many of these (definitely not ';' !)
\end{code}

Anything else is a symbol (for now.)
\begin{code}
issymbol c
  | isSpace c  =  False
  | isDigit c  =  False
  | isAlpha c  =  False
  | c `elem` decorChar : openings ++ closings ++ separators  = False
  | otherwise  = True
\end{code}

Now we define the lexer:
\begin{code}
tlex :: String -> [TToken]
tlex "" = []
tlex str@(c:cs)
  | isSpace c  =  tlex cs
  | isDigit c  =  tlexNum [c] cs
  | c == '-'  =  tlexMinus cs
  | isAlpha c      =  tlexId False [c] cs
  | c == decorChar =  tlexId True  [c] cs
  | c `elem` openings  =  TOpen [c] : tlex cs
  | c `elem` closings  =  TClose [c] : tlex cs
  | c `elem` separators  =  TSep [c] : tlex cs
  | otherwise  =  tlexSym [c] cs
\end{code}

Just digits
\begin{code}
tlexNum mun ""  = [ TNum $ reverse mun ]
tlexNum mun str@(c:cs)
  | isDigit c  =  tlexNum (c:mun) cs
  | otherwise  =  TNum (reverse mun) : tlex str

tlexMinus "" = [ TSym "-" ]
tlexMinus str@(c:cs)
  | isDigit c  =  tlexNum [c,'-'] cs
  | issymbol c  =  tlexSym [c,'-'] cs
  | otherwise  =  TSym "-" : tlex str
\end{code}

\newpage
A \texttt{decorChar}  will end an identifier,
if none exists at the start.
Otherwise it is an error.
Also a subscript appearing when a \texttt{decorChar}is laready present
is an error.
\begin{code}
tlexId _ di ""  = [ TId $ reverse di ]
tlexId hasDC di str@(c:cs)
  | isAlpha c  =  tlexId hasDC (c:di) cs
  | isDigit c  =  tlexId hasDC (c:di) cs
  | c == '_'
      = if hasDC then (derr c di) : tlex cs
                 else tlexDuring (c:di) [] cs
  | c == decorChar
      = if hasDC then (derr c di) : tlex cs
                 else TId (reverse (c:di)) : tlex cs
  | otherwise  = TId (reverse di) : tlex str
  where derr c di = Terr ("Overdecorated: " ++ reverse (c:di))

tlexDuring di ""  ""  =  [ Terr ("Missing subscript: " ++ reverse di) ]
tlexDuring di bus ""  =  [ TId (reverse di ++ reverse bus) ]
tlexDuring di bus str@(c:cs)
  | isAlpha c  =  tlexDuring di (c:bus) cs
  | otherwise =  TId (reverse di ++ reverse bus) : tlex str
\end{code}

\begin{code}
tlexSym mys ""  = [ TSym $ reverse mys ]
tlexSym mys str@(c:cs)
  | issymbol c  =  tlexSym (c:mys) cs
  | otherwise  =  TSym (reverse mys) : tlex str
\end{code}

\subsection{Simple Term Parser}

The abstract syntax:
\begin{eqnarray*}
   b &\in& Bool
\\ n &\in& Num
\\ i &\in& Ident
\\ v &\in& Var = Ident \times \dots
\\ t &\in& Term ::= b
               \mid n
               \mid v
               \mid i~(t_1,\dots,t_n)
               \mid \mathcal Q ~i ~\lst v \bullet t
\end{eqnarray*}

The concrete syntax (non-terminals in <..>):
\begin{verbatim}
 <t> ::= <b> | n | v | i ( t , ... , t ) | <q> i <v$> , ... ,<v$> @ <t>
 <b> ::= true | false
 <q> ::= QS | QL
 <v$> ::=  v | v $
 -- keywords: true false QS QL
\end{verbatim}
\begin{code}
keyTrue = "true"
keyFalse = "false"
keySetBind = "QS"
keyListBind = "QL"
\end{code}

\begin{code}
true = Vbl (fromJust $ ident "true") PredV Static
trueP = fromJust $ pVar true
false = Vbl (fromJust $ ident "false") PredV Static
falseP = fromJust $ pVar false
\end{code}


Top level term parsers.
\begin{code}
sTermParse :: Monad m => TermKind -> [TToken] -> m (Term, [TToken])
sTermParse tk [] =  fail "sTermParse: nothing to parse"

sTermParse tk (TNum str:tts)
  = return ( Val tk $ Integer $ read str, tts)
sTermParse tk (TId str:tts)
  | str == keyTrue   = return ( mkTrue tk,  tts)
  | str == keyFalse  = return ( mkFalse tk, tts)
  | str == keySetBind = fail "sTermParse: var-set binders NYI"
  | str == keyListBind = fail "sTermParse: var-list binders NYI"
  | otherwise = sIdParse tk (repmacro str) tts
sTermParse tk (tt:tts)  = fail ("sTermParse: unexpected token: "++show tt)

mkTrue P   =  trueP
mkTrue (E _)
  =  Val (E $ GivenType (fromJust $ ident $ _mathbb "B")) $ Boolean True
mkFalse P  =  falseP
mkFalse (E _)
  =  Val (E $ GivenType (fromJust $ ident $ _mathbb "B")) $ Boolean False

repmacro "" = ""
repmacro (c:cs)
 | c == '_'  = findmacro "_" cs
 | otherwise  =  c : repmacro cs

findmacro orcam ""
 = case findSym macro of
    Nothing   ->  macro
    Just rep  ->  rep
 where macro = reverse orcam

-- simple for now - we assume macro runs to end of string.
findmacro orcam (c:cs) = findmacro (c:orcam) cs
\end{code}

Seen an identifier, check for an opening parenthesis:
\begin{code}
sIdParse tk id1 tts = fail ("sIdParse NYI, given: "++id1)
\end{code}

Handy specialisations:
\begin{code}
sExprParse :: Monad m => String -> m (Term, [TToken])
sExprParse = sTermParse (E ArbType) . tlex
sPredParse :: Monad m => String -> m (Term, [TToken])
sPredParse = sTermParse P . tlex
\end{code}

\subsection{Random test/prototype bits}

\begin{code}
showMacro :: String -> IO ()
showMacro macro
 = case findSym macro of
     Nothing -> putStrLn "<nothing found>"
     Just sym -> putStrLn ("found: "++sym)
\end{code}
