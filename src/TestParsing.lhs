\section{Test Parsing}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TestParsing (
  mkLawName
, sExprParse
, sPredParse
)

where

import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
-- import qualified Data.Set as S
import Data.List (nub, sort, (\\), intercalate)
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
    Just integers for now,
    with a minus-sign to start if negative,
    with no whitespece between it and the one or more (decimal) digits.
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
data TToken
  =  TNum   Integer
  |  TId    Identifier VarWhen
  |  TOpen  String
  |  TClose String
  |  TSep   String
  |  TSym   Identifier
  |  TErr   String
  deriving (Eq,Show)
\end{code}

We shall use decoration to indicate variable temporality.
We use underscore for ``During'',
and a designated character (`\texttt{?}')
to indicate ``Before'' or ``After''.

\begin{tabular}{|l|c|l|}
\hline
  Temp. & Math. & String
\\\hline
  Static & $v$ & \texttt{v}
\\\hline
  Before & $v$ & \texttt{?v}
\\\hline
  During & $v_m$ & \texttt{v\_m}
\\\hline
  After & $v'$ & \texttt{v?}
\\\hline
\end{tabular}

We chose the character `?' because
it is on both Apple, Windows and ``unix'' keyboards,
and is not really used for anything else in a math context.
\begin{code}
whenChar = '?'
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
  | c `elem` whenChar : openings ++ closings ++ separators
               =  False
  | otherwise  =  True
\end{code}

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
    (root,rest) = break (== '_') cs
    have [] = False ; have _ = True
    subscr = ttail rest
    ttail [] = [] ; ttail (_:cs) = cs

-- tail recursion often requires reversal at end of accumulated lists
mkMys  =  mkSym . reverse   ;   mkDi   =  mkId . reverse
\end{code}

Now we define the lexer:
\begin{code}
tlex :: String -> [TToken]
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
  | c == '_'             =  tlexMacro [c] cs
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

tlexMinus "" = [ mkSym "-" ]
tlexMinus str@(c:cs)
  | isDigit c  =  tlexNum [c,'-'] cs
  | issymbol c  =  tlexSym [c,'-'] cs
  | otherwise  =  mkSym "-" : tlex str
\end{code}

A \texttt{whenChar}  will end an identifier,
if none exists at the start.
Otherwise it is an error.
Also a subscript appearing when a \texttt{whenChar}is laready present
is an error.
\begin{code}
tlexId _ di ""  = [ mkDi di ]
tlexId hasDC di str@(c:cs)
  | isAlpha c  =  tlexId hasDC (c:di) cs
  | isDigit c  =  tlexId hasDC (c:di) cs
  | c == '_'
      = if hasDC then (derr c di) : tlex cs
                 else tlexDuring (c:di) [] cs
  | c == whenChar
      = if hasDC then (derr c di) : tlex cs
                 else  mkDi (c:di) : tlex cs
  | otherwise  =  mkDi di : tlex str
  where
    derr c di = TErr ("Overdecorated: " ++ reverse (c:di))

tlexDuring di ""  ""  =  [ TErr ("Missing subscript: " ++ reverse di) ]
tlexDuring di bus ""  =  [ mkId (reverse di ++ reverse bus) ]
tlexDuring di bus str@(c:cs)
  | isAlpha c  =  tlexDuring di (c:bus) cs
  | otherwise  =  mkId (reverse di ++ reverse bus) : tlex str
\end{code}

\begin{code}
tlexMacro orcam "" = [ mkCam orcam ]
tlexMacro orcam str@(c:cs)
 | isAlpha c  =  tlexMacro (c:orcam) cs
 | otherwise  =  mkCam orcam : tlex str

mkCam = mkMac . reverse
mkMac macro
  = case findSym macro of
      Nothing  ->  TErr ("Invalid macro: "++macro)
      Just str
       -> case ident str of
            But msgs -> TErr ("Macro expansion bad: "++unlines' msgs)
            Yes i -> TSym i
\end{code}

\begin{code}
tlexSym mys ""  = [ mkMys mys ]
tlexSym mys str@(c:cs)
  | issymbol c  =  tlexSym (c:mys) cs
  | otherwise  =  mkMys mys : tlex str
\end{code}

\subsection{Law Name Parser}

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

The concrete syntax (non-terminals in \verb@<..>@):
\begin{verbatim}
 <b> ::= true | false
 <q> ::= QS | QL
 <v$> ::=  v | v $
 <t> ::= <b> | n | v | i ( t , ... , t ) | <q> i <v$> , ... ,<v$> @ <t>
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


\subsubsection{Top level term parser}

\begin{code}
sTermParse :: MonadFail m => TermKind -> [TToken] -> m (Term, [TToken])
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

mkTrue P   =  trueP
mkTrue (E _)
  =  Val (E $ GivenType (fromJust $ ident $ _mathbb "B")) $ Boolean True
mkFalse P  =  falseP
mkFalse (E _)
  =  Val (E $ GivenType (fromJust $ ident $ _mathbb "B")) $ Boolean False
\end{code}


Seen an identifier, check for an opening parenthesis:
\begin{code}
sIdParse tk id1 vw (TOpen "(" : tts)  =  sAppParse tk id1 [] tts
sIdParse tk id1 vw tts                =  return (mkVar tk id1 vw, tts)
\end{code}

Making a variable term:
\begin{code}
mkVar P id1 vw   =  fromJust $ var P $ Vbl id1 PredV vw
mkVar tk id1 vw  =  fromJust $ var tk $ Vbl id1 ObsV vw
\end{code}

Seen identifier and opening parenthesis.
Look for sub-term, or closing parenthesis.
\begin{code}
sAppParse tk id1 smretbus (TClose ")" : tts)
  = return ( Cons tk id1 $ reverse smretbus, tts)
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
  =  return ( Cons tk id1 $ reverse smretbus, tts)
sAppParse' tk id1 smretbus tts
  =  fail ("sAppParse': expected ',' or ')'")
\end{code}

Handy specialisations:
\begin{code}
sExprParse :: MonadFail m => String -> m (Term, [TToken])
sExprParse = sTermParse (E ArbType) . tlex
sPredParse :: MonadFail m => String -> m (Term, [TToken])
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

\begin{code}
tparse = putStrLn . trTerm 0 . fst . fromJust .sPredParse
\end{code}
