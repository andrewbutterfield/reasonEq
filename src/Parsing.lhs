\chapter{Parsing}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Parsing (
  mkLawName
, s_syntax
, termParse
)

where

import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
-- import qualified Data.Set as S
import Data.List (nub, sort, (\\), intercalate)
import Data.Char


import YesBut
import Utilities
import Symbols
import LexBase
import Variables
import AST
import SideCond
import TestRendering
\end{code}

\section{Parsing Intro.}

We provide a simple, clunky way to parse terms,
in prefix-style only.

For now we have simple literals,
composites done as prefix-functions applied to delimited lists of sub-terms,
and binders in standard mixfix style.

\newpage

\section{Lexical Basics}

\subsection{Tokens}

We have the following token classes:
\begin{description}
  \item [Numbers]~
    Just integers for now,
    with a minus-sign to start if negative,
    with no whitespace between it and the one or more (decimal) digits.
  \item [Identifiers]~
    Identifiers as per \texttt{LexBase},
    with added decoration for variable classification
    and unicode macro expansion.
    \textbf{Keywords} form a subset of these.
    We expect identifiers to have one of the following concrete forms:
    \textsf{ident},
    \texttt{?}\textsf{ident},
    \textsf{ident}\texttt{?},
    \textsf{indent}\texttt\_\textsf{alphas},
    \texttt{\_}\textsf{macro}.
    We only expect the ``dangling space'' permitted in identifiers
    to arise as the result of macro expansion.
  \item [Delimiters]~
    Small tokens used for general punctuation,
    further classified into: matched (Open/Close) bracketing; and separators.
  \item [Symbols]~
    Tokens assembled from everything else,
    provided they satisfy \texttt{LexBase.validIdent}.
\end{description}

\begin{code}
data Token
  =  TNum   Integer
  |  TId    Identifier VarWhen
  |  TOpen  String
  |  TClose String
  |  TSep   String
  |  TSym   Identifier
  |  TErr   String
  deriving (Eq,Show)
\end{code}

We shall use the question-mark as a decoration to indicate variable temporality.
We choose this character because
it is on both Apple, Windows and ``unix'' keyboards,
and is not really used for anything else in a math context.
\begin{code}
whenChar = '?'
\end{code}

\begin{tabular}{|l|c|l|}
\hline
  Temp. & Math. & String
\\\hline
  Static & $v$ & \texttt{v}
\\\hline
  Before & $v$ & \texttt{?v}
\\\hline
  During & $v_m$ & \texttt{v?m}
\\\hline
  After & $v'$ & \texttt{v?}
\\\hline
\end{tabular}


\subsection{Character Classes}

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
  | c `elem` whenChar : openings ++ closings ++ separators
               =  False
  | otherwise  =  True
\end{code}

\subsection{Word Classes}

Making symbols and identifiers:
\begin{code}
mkSym str
  = case ident str of
      But msgs  ->  TErr $ unlines' msgs
      Yes i     ->  TSym i

mkId str
  = case ident str of
      But msgs  ->  TErr $ unlines' msgs
      Yes i     ->  let (i',vw') = extractTemporality i str
                    in TId i' vw'

extractTemporality i cs -- non-empty
 | c1 == whenChar       =  ( fromJust $ ident $ tail cs, Before)
 | last cs == whenChar  =  ( fromJust $ ident $ init cs, After )
 | have root && have subscr && all isAlpha subscr
                        =  ( fromJust $ ident root,      During subscr )
 | otherwise = ( i, Static )
 where
    c1 = head cs
    (root,rest) = break (== whenChar) cs
    have [] = False ; have _ = True
    subscr = ttail rest
    ttail [] = [] ; ttail (_:cs) = cs

-- tail recursion often requires reversal at end of accumulated lists
mkMys  =  mkSym . reverse   ;   mkDi   =  mkId . reverse
\end{code}

Now we define the lexer:
\begin{code}
tlex :: String -> [Token]
tlex "" = []
tlex str@(c:cs)
  | isSpace c            =  tlex cs
  | isDigit c            =  tlexNum [c] cs
  | c == '-'             =  tlexMinus cs
  | isAlpha c            =  tlexId False [c] cs
  | c == whenChar        =  tlexId True  [c] cs
  | c `elem` openings    =  TOpen [c]  : tlex cs
  | c `elem` closings    =  TClose [c] : tlex cs
  | c `elem` separators  =  TSep [c]   : tlex cs
  | otherwise            =  tlexSym [c] cs
\end{code}

\newpage
Just digits
\begin{code}
tlexNum mun ""  = [ mkNum mun ]
tlexNum mun str@(c:cs)
  | isDigit c  =  tlexNum (c:mun) cs
  | otherwise  =  mkNum mun : tlex str

mkNum mun = TNum $ read $ reverse mun
\end{code}

We have seen a minus sign. If followed immediately by a number
it is then merged with it to form a negative literal.
Otherwise it is treated as a symbol.
\begin{code}
tlexMinus "" = [ mkSym "-" ]
tlexMinus str@(c:cs)
  | isDigit c  =  tlexNum [c,'-'] cs
  | otherwise  =  mkSym "-" : tlex str
\end{code}

A \texttt{whenChar} may end an identifier,
or indicate that we expect a During subscript,
provided none exists at the start.
Otherwise it is an error.
Also a subscript appearing when a \texttt{whenChar} is already present
is an error.
\begin{code}
-- note, the di component is never empty when this is called
tlexId _ di ""  = [ mkDi di ]
tlexId hasDC di str@(c:cs)
  | isAlpha c  =  tlexId hasDC (c:di) cs
  | isDigit c  =  tlexId hasDC (c:di) cs
  | c == whenChar
      = if hasDC then (derr c di) : tlex cs
                 else  tlexDuring (c:di) [] cs
  | otherwise  =  mkDi di : tlex str
  where
    derr c di = TErr ("Overdecorated: " ++ reverse (c:di))

tlexDuring di ""  ""  =  [ mkDi di ]
tlexDuring di bus ""  =  [ mkId (reverse di ++ reverse bus) ]
tlexDuring di bus str@(c:cs)
  | isAlpha c  =  tlexDuring di (c:bus) cs
  | otherwise  =  mkId (reverse di ++ reverse bus) : tlex str
\end{code}

If none of the above apply, we parse a maximum-munch symbol:
\begin{code}
tlexSym mys ""  = [ mkMys mys ]
tlexSym mys str@(c:cs)
  | issymbol c  =  tlexSym (c:mys) cs
  | otherwise  =  mkMys mys : tlex str
\end{code}

\section{Law Name Parser}

\begin{code}
mkLawName :: [String] -> String
mkLawName ss
  = intercalate "_" $ map showTTok $ concat $ map tlex ss
  where
    showTTok (TNum n)  = show n
    showTTok (TId i _) = idName i
    showTTok (TSym i)  = idName i
    showTTok ttok      = _redQ
\end{code}

\section{Simple Term Parser}

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

The concrete syntax (non-terminals in \verb@<..>@):
\begin{code}
s_syntax
 = [ "Lexical Tokens:"
   , "n : int with optional leading minus"
   , "i : reasonEq identifier"
   , "v ::= i | ?i | i? | i?i"
   , "Term Syntax:"
   , "<b> ::= true | false"
   , "<q> ::= QS | QL"
   , "<v$> ::=  v | v $"
   , "<t> ::= <b> | n | v | i ( t , ... , t ) | <q> i <v$> , ... ,<v$> @ <t>"
   , "keywords: true false QS QL"
   , "keysymbols: ? $ ( , ) @"
   ]

keyTrue = "true"
keyFalse = "false"
keySetBind = "QS"
keyListBind = "QL"
keyLstVar = "$"
keySep = ","
keyQBody = "@"
\end{code}



\begin{code}
true = Vbl (fromJust $ ident "true") PredV Static
trueP = fromJust $ pVar ArbType true
false = Vbl (fromJust $ ident "false") PredV Static
falseP = fromJust $ pVar ArbType false
\end{code}

\newpage

\subsection{Top level term parser}

\begin{code}
sTermParse :: MonadFail m => Type -> [Token] -> m (Term, [Token])
sTermParse tk [] =  fail "sTermParse: nothing to parse"

sTermParse tk (TNum n:tts)
  = return ( Val tk $ Integer n, tts)
sTermParse tk (TId i vw:tts)
  | n == keyTrue      =  return ( mkTrue tk,  tts)
  | n == keyFalse     =  return ( mkFalse tk, tts)
  | n == keySetBind   =  fail "sTermParse: var-set binders NYI"
  | n == keyListBind  =  fail "sTermParse: var-list binders NYI"
  | otherwise         =  sIdParse tk i vw tts
  where n = idName i
sTermParse tk (TSym i:tts) = sIdParse tk i Static tts
sTermParse tk (tt:tts)  = fail ("sTermParse: unexpected token: "++show tt)

mkTrue t | isPType t  =  trueP
mkTrue _
  =  Val (GivenType (fromJust $ ident $ _mathbb "B")) $ Boolean True
mkFalse t | isPType t  =  falseP
mkFalse _
  =  Val (GivenType (fromJust $ ident $ _mathbb "B")) $ Boolean False
\end{code}


Seen an identifier, check for an opening parenthesis:
\begin{code}
sIdParse tk id1 vw (TOpen "(" : tts)  =  sAppParse tk id1 [] tts
sIdParse tk id1 vw tts                =  return (mkVar tk id1 vw, tts)
\end{code}

Making a variable term:
\begin{code}
mkVar tp id1 vw 
  | isPType tp  =  fromJust $ var tp $ Vbl id1 PredV vw
  | otherwise   =  fromJust $ var tp $ Vbl id1 ObsV  vw
\end{code}

Seen identifier and opening parenthesis.
Look for sub-term, or closing parenthesis.
\begin{code}
sAppParse tk id1 smretbus (TClose ")" : tts)
  = return ( Cons tk True id1 $ reverse smretbus, tts)
sAppParse tk id1 smretbus tts
  = do (tsub',tts') <- sTermParse tk tts
       sAppParse' tk id1 (tsub':smretbus) tts'
\end{code}

Seen (sub-) term.
Looking for comma or closing parenthesis
\begin{code}
sAppParse' tk id1 smretbus (TSep "," : tts)
  =  sAppParse tk id1 smretbus tts
sAppParse' tk id1 smretbus (TClose ")" : tts)
  =  return ( Cons tk True id1 $ reverse smretbus, tts)
sAppParse' tk id1 smretbus tts
  =  fail ("sAppParse': expected ',' or ')'")
\end{code}

Handy specialisations:
\begin{code}
termParse :: MonadFail m => String -> m (Term, [Token])
termParse = sTermParse arbpred . tlex
\end{code}

\newpage
\section{Random test/prototype bits}

\begin{code}
showMacro :: String -> IO ()
showMacro macro
 = case findSym macro of
     Nothing -> putStrLn "<nothing found>"
     Just sym -> putStrLn ("found: "++sym)
\end{code}

\begin{code}
tparse str 
  = case termParse str of
      Yes (term,tokens) 
        | null tokens -> putStrLn $ trTerm 0 term
        | otherwise   -> putStrLn ("tokens leftover: "++show tokens)
      But msgs -> putStrLn $ unlines' msgs
\end{code}
