\chapter{Theory Load and Save}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LoadSave (
  mkLawName
, term_syntax
, renderToken'
, loadTheory, saveTheory
, loadTerm
)

where

import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (nub, sort, (\\), intercalate)
import Data.Char


import YesBut
import Control
import Utilities
import Symbols
import LexBase
import Variables
import Types
import AST
import SideCond
import Laws
import VarData
import Assertions
import Theories
import TestRendering
import StdTypeSignature

import Debugger
\end{code}

\section{Load-Save Intro.}

We provide a simple, clunky way to read and write theory objects
using a simple grammar mostly using prefix-based constructs.

The plan is that we will use this as the main way to create
new theories,
so we don't have to use Haskell modules.

For now we have simple literals,
composites done as prefix-functions applied to delimited lists of sub-terms,
and binders in standard mixfix style.

In general we will take a text file,
and add line numbers, and remove blank lines before processing.

\begin{code}
type NumberedLine = (Int,String)
prepare :: String -> [NumberedLine]
prepare 
  = filter nonNull . zip [1..] . lines
  where nonNull (_,string) = not $ all isSpace string
\end{code}


\newpage
\section{Theories}

We start here with code to load and save \emph{entire} theories
We will gradually flesh this out.

For now we concern ourselves with theory names, dependencies, knowns, laws,
and conjectures.
Proofs are complex, and only arise by running \reasonEq,
and we will rely on dump and grab (export and import?) to handle them.
The automatic laws can be re-generated once the theory is loaded.

Here is a first cut for a theory:
\begin{verbatim}
Theory <TheoryName>
DependsOn 
  <DepThryName>  ... 
  <DepThryName>  ...
Done
KnownVariables
  <entry> 
  ... 
Done
Laws  
  <law> 
  ...
Done
Conjectures
  <conj> 
  ... 
Done
\end{verbatim}
The theory name should be first,
while all the other ``WhatThisIs''\dots Done sections
can occur in any order, and multiple times.
Their contents are gathered and kept in sequence.
When we output theories like this, 
each section will appear once in the above order.

Keywords:
\begin{code}
kTheory = "Theory"
kDependsOn = "DependsOn"
kKnownVariables = "KnownVariables"
kLaws = "Laws"
kConjectures = "Conjectures"
kDone = "Done"
\end{code}

\subsection{Load Theory}

Theory names become filenames,
so they are restricted to the ``safe'' character set 
less the extension dot: \verb"[a-zA-Z0-9-_]",
\begin{code}
validFileName name = all validFileChar name
validFileChar c = c `elem` validFileChars
validFileChars = ['a'..'z'] ++ ['A'..'Z'] ++ "_-"
\end{code}


\begin{code}
loadTheory :: MonadFail mf => String -> mf Theory
loadTheory text  =  importTheory nullTheory $ prepare text


importTheory :: MonadFail mf  => Theory -> [(NumberedLine)] -> mf Theory
importTheory thry [] = fail "Empty theory file!"
importTheory thry ((lno,headline):rest)
  = case words headline of
      [key,name] | key == kTheory && validFileName name 
         -> importBodies (thName_ name thry) rest      
      _  ->  fail $ unlines [ "loadTheory headline parse error at line "
                              ++ show lno 
                            , "  expected: "++kTheory++" theoryname"
                            , "  got: " ++ headline
                            ]

importBodies :: MonadFail mf => Theory -> [(NumberedLine)] -> mf Theory  
importBodies thry []  =  return thry
importBodies thry nlines@((lno,blockheader):rest)
  | blockheader == kDependsOn  =  importDeps thry [] rest
  | blockheader == kConjectures  =  importConjs thry [] rest
  | blockheader `elem` [kKnownVariables,kLaws]
    = fail $ unlines
       [ "loadTheory not yet able to handle "++blockheader 
         ++" at line "++show lno
       , "got so far: " ++ show thry
       ]
  | otherwise
      = fail $ unlines [ "loadTheory expected block header at " ++ show lno
                       , "got: "++blockheader
                       ] 

importDeps thry sped [] 
  = fail $ unlines [ "premature file end after "++kDependsOn ]
importDeps thry sped ((lno,line):rest) 
  | line == kDone  
     =  importBodies (thDeps__ (++(reverse sped)) thry) rest
  | otherwise = importDepLine thry sped rest lno $ words line

importDepLine thry sped rest lno [] = importDeps thry sped rest
importDepLine thry sped rest lno (dep:deps)
  | validFileName dep = importDepLine thry (dep:sped) rest lno deps
  | otherwise = fail $ unlines
     [ "invalid dependency at line "++show lno
     , "  saw "++dep ]
\end{code}


\subsection{Save Theory}

\begin{code}
saveTheory :: Theory -> String
saveTheory theory = unlines (
  (kTheory ++ " " ++ thName theory)
   : ( saveDeps (thDeps theory) ++
       saveKnownVars (known theory) ++
       saveTheLaws (laws theory) ++
       saveConjs (conjs theory)        ) )

saveDeps [] = []
saveDeps deps = 
  [ kDependsOn , saveIndentedNameList 2 80 deps , kDone] 

saveKnownVars vtab@(VarData (name,vtable,stable,dtable))
  | M.null vtable && M.null stable && M.null dtable  =  []
  | otherwise = [ "" , kKnownVariables , saveVarTable vtab , kDone ]

saveTheLaws [] = []
saveTheLaws laws =  [ "" , kLaws , saveLaws laws, kDone ] 

saveConjs [] = []
saveConjs conjs = [ "" , kConjectures , saveConjectures conjs, kDone ] 
\end{code}

\newpage
\section{VarTables}

\subsection{Load VarTable}

\begin{code}
loadVarTable :: MonadFail mf => String -> mf VarTable
loadVarTable text = fail "loadVarTable NYI"
\end{code}

\subsection{Save VarTable}

\begin{code}
saveVarTable :: VarTable -> String
saveVarTable (VarData (vtname,vtable,stable,dtable)) = unlines' $ 
  [ "  variables " ++ show (M.size vtable)
  , "  listvars " ++ show (M.size stable)
  , "  dynamics " ++ show (M.size dtable)
  ]
\end{code}

\newpage
\section{Laws}

\subsection{Load Laws}

A law starts on a new line,
but can also involve many lines.

\begin{code}
loadLaws :: MonadFail mf => String -> mf [Law]
loadLaws text = fail "loadLaws NYI"
\end{code}

\subsection{Save Laws}


\begin{code}
saveLaws :: [Law] -> String
saveLaws laws = unlines' $ 
  [ "  laws " ++ show (length laws)
  ]
\end{code}

\subsection{Load Conjectures}

A conjecture starts on a new line,
but can also involve many lines.

\begin{code}
loadConjectures :: MonadFail mf => String -> mf [NmdAssertion]
loadConjectures text = fail "loadConjectures NYI"


importConjs :: MonadFail mf 
            => Theory -> [NmdAssertion] -> [NumberedLine] -> mf Theory
importConjs thry sjnoc []
  = fail $ unlines [ "premature file end after "++kConjectures ]
importConjs thry sjnoc ((lno,line):rest)
  | line == kDone
     =  importBodies (conjs__ (++(reverse sjnoc)) thry) rest
  | otherwise  = importConjecture thry sjnoc rest lno line

importConjecture thry sjnoc rest lno line
 = fail "importConjecture NYI"

\end{code}

\subsection{Save Conjectures}

\begin{code}
saveConjectures :: [NmdAssertion] -> String
saveConjectures nmdassns  =  unlines' $ map saveConjecture nmdassns
\end{code}
Possible format: {\color{red}\verb"name % term % sidecondition ."}
with arbitrary line breaks?
\begin{code}
saveConjecture :: NmdAssertion -> String
saveConjecture (name,Assertion tm sc)
  = unlines' $ map ("  "++) [name,"%",saveTerm tm,"%","scText","."]
\end{code}

\newpage
\section{Terms}

The abstract syntax:
\begin{eqnarray*}
   b &\in& Bool
\\ n &\in& Num
\\ i &\in& Ident
\\ s &\in& \setof{nonsub,cansub}
\\ v &\in& Var = Ident \times VarWhen
\\ \lst v &\in& LVar = Var \times Less
\\ g &\in& GVar =  Var \uplus LVar
\\ gs &\in& GVarList = GVar^*
\\ T &\in& Type
\\ t &\in& Term ::= b
               \mid n
               \mid v
               \mid i~s~(t_1,\dots,t_n)
               \mid \mathcal Q ~i ~gs \bullet t
               \mid \mathcal X ~i ~t
               \mid v : T
\\ && \quad \mid t [t_1,\dots,t_n/g_1,\dots,g_n]
\\ && \quad \mid \mathcal I ~i_{top} ~ s_{top} ~i_{ix} ~ s_{ix} 
                    ~(\lst v_1,\dots,\lst v_n)
\\ && \quad \mid (~t~)
\end{eqnarray*}

The concrete syntax (non-terminals in \verb@<..>@):
\begin{code}
term_syntax
 = [ "** Lexical Tokens:"
   , "n : int with optional leading minus"
   , "i : reasonEq identifier"
   , "s : substitutability non(N) can(S))"
   , "** Variable Syntax:"
   , "<v> ::= i | 'i | i' | i'i"
   , "by default lowercase i are ObsVar, uppercase are TermVar"
   , "we could have more nuanced defaults"
   , "we could declare variables seperately and post-process them"
   , "should the known variables (so far) be passed as a parameter?"
   , "<lv> ::= <v>$"
   , "<gv> ::=  <v> | <lv>"
   , "** Term Syntax:"
   , "<b> ::= true | false"
   , "<q> ::= QS | QL"
   , "<t> ::= <b>  |  n  |  <v>"
   , "     |  i s ( <t> , ... , <t> )"
   , "     |  <q> i <gv> ... <gv> @ <t>"
   , "** Keywords:   true  false  QS  QL"
   , "** Keysymbols: ?  $  (  ,  )  @"
   ]

kTrue = "true"
kFalse = "false"
kSetBind = "QS"
kListBind = "QL"
kLstVar = '$'
kSep = ','
kQBody = "@"
\end{code}


\subsection{Save Term}

\begin{code}
saveTerm :: Term -> String
saveTerm (Val typ (Boolean b)) = if b then kTrue else kFalse
saveTerm (Val typ (Integer i)) = show i
saveTerm (Var typ var) = saveVariable var
saveTerm (Cons typ subable nm terms) = "C-stuff?"
saveTerm (Bnd typ n vs term) = "B-stuff?"
saveTerm (Lam typ n vl term) = "L-stuff?"
saveTerm (Cls typ term) = "X-stuff?"
saveTerm (Sub typ term sub) = "S-stuff?"
saveTerm (Iter typ sa na si ni lvs) = "I-stuff?"
saveTerm (VTyp typ var) = "VT-stuff?"
\end{code}



\subsection{Load Term}




Truth builders:
\begin{code}
true = Vbl (fromJust $ ident "true") PredV Static
trueP = fromJust $ pVar ArbType true
false = Vbl (fromJust $ ident "false") PredV Static
falseP = fromJust $ pVar ArbType false
mkTrue n | isUpper $ head n  =  trueP
mkTrue _ =  Val bool $ Boolean True
mkFalse n | isUpper $ head n  =  falseP
mkFalse _  =  Val bool $ Boolean False
\end{code}

Making variables and variable-terms

For now the variable class is determined by the first character
of the identifier.
The simplest is the case, lower being an observable, higher a term.


\begin{code}
mkV id1 vw 
  | isUpper $ head iname  =  Vbl id1 PredV vw
  | otherwise             =  Vbl id1 ObsV  vw
  where iname = idName id1

mkLV id1 vw  = LVbl (mkV id1 vw) [] []

mkVarTerm id1 vw  =  fromJust $ var arbpred $ mkV id1 vw

tok2GVar (TId i vw)    = StdVar $ mkV i vw
tok2GVar (TLVar i vw ) = LstVar $ mkLV i vw
\end{code}


\newpage

\subsection{Term Reader}

\begin{code}
sTermRead :: MonadFail m => [Token] -> m (Term, [Token])
sTermRead [] =  fail "sTermRead: nothing to parse"
\end{code}

\paragraph{Numbers}

\begin{code}
sTermRead (TNum n:tts) = return ( Val int $ Integer n, tts)
\end{code}

\paragraph{Symbols}

\begin{code}
sTermRead (TSym i:tts) = sIdParse i Static tts
\end{code}

\paragraph{Identifiers}

\begin{code}
sTermRead (TId i vw:tts)
  | n == kTrue      =  return ( mkTrue n,  tts)
  | n == kFalse     =  return ( mkFalse n, tts)
  | n == kSetBind   =  setQParse tts
  | n == kListBind  =  listQParse tts
  | otherwise         =  sIdParse i vw tts
  where n = idName i
\end{code}

\paragraph{Bad Start}

\begin{code}
sTermRead (tt:tts)  = fail ("sTermRead: unexpected token: "++renderToken tt)
\end{code}

\paragraph{Constructions}

Seen an identifier, check for a substitutability indicator,
followed by an opening parenthesis:
\begin{code}
sIdParse id1 vw (TId (Identifier subable _) _ : TOpen "(" : tts)
  |  subable == "N"  =  sAppParse id1 False [] tts
  |  subable == "S"  =  sAppParse id1 True  [] tts
sIdParse id1 vw tts  =  return (mkVarTerm id1 vw, tts)
\end{code}


Seen identifier and opening parenthesis.
$$ i(~~~t_1,\dots,t_n) $$
Look for sub-term, or closing parenthesis.
\begin{code}
sAppParse id1 subable smretbus (TClose ")" : tts)
  = return ( Cons arbpred subable id1 $ reverse smretbus, tts)
sAppParse id1 subable smretbus tts
  = do (tsub',tts') <- sTermRead tts
       sAppParse' id1 subable (tsub':smretbus) tts'
\end{code}

\newpage
Seen (sub-) term.
Looking for comma or closing parenthesis
\begin{code}
sAppParse' id1 subable smretbus (TSep "," : tts)
  =  sAppParse id1 subable smretbus tts
sAppParse' id1 subable smretbus (TClose ")" : tts)
  =  return ( Cons arbpred subable id1 $ reverse smretbus, tts)
sAppParse' id1 subable smretbus tts
  =  fail ("sAppParse': expected ',' or ')'")
\end{code}

\paragraph{Quantifiers}~

Seen \texttt{QS}, 
$$ QS~~~i~g_1 \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
setQParse [] = fail "setQParse: premature end"
setQParse (TId i Static : tts) = do
  (i,sg,term,tts') <- quantread i [] tts
  qsterm <- pBnd i (S.fromList $ map tok2GVar sg) term
  return (qsterm,tts')
setQParse (tok:_) = fail ("setQParse: exp. ident, found: "++renderToken tok)
\end{code}

Seen \texttt{QL}, 
$$ QL~~~i~g_1 \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
listQParse [] = fail "listQParse: premature end"
listQParse (TId i Static : tts) = do
  (i,sg,term,tts') <- quantread i [] tts
  lsterm <- pLam i (reverse $ map tok2GVar sg) term
  return (lsterm,tts')
listQParse (tok:_) = fail ("listQParse: exp. ident, found: "++renderToken tok)
\end{code}

Seen \texttt{Qx i}, and zero or more \texttt{g\_i}:
$$ Qx~i~g_1 \dots g_i ~~~~~ g_{i+1} \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
quantread i _ [] = fail ("quantread: "++trId i++" (premature end)")
quantread i sg (TSym s : tts)
  | idName s == kQBody  =  quantreadBody i sg tts
quantread i sg (v@(TId _ _)    : tts)   =  quantread i (v:sg) tts
quantread i sg (lv@(TLVar _ _) : tts)   =  quantread i (lv:sg) tts
quantread i sg (tok : _)  = fail ("quantread: unexpected token "++renderToken tok)
\end{code}

Seen \texttt{Qx i g\_1 .. g\_n @}, 
$$ Qx~i~g_1 \dots g_n \bullet ~~~ t $$
parse the body term
\begin{code}
quantreadBody i _ [] = fail ("quantread: "++trId i++" (missing body)")
quantreadBody i sg tts = do
  (term,toks) <- sTermRead tts
  return (i,sg,term,toks)
\end{code}

\subsubsection{Top-Level Term Reader}

\begin{code}
loadTerm :: MonadFail mf => String -> mf (Term, [Token])
loadTerm = sTermRead . tlex
\end{code}


\section{Variables}


\subsection{Save Variable}

\begin{code}
saveVariable :: Variable -> String
saveVariable (Vbl i vc Before)      = '\'' : idName i
saveVariable (Vbl i vc (During d))  =  idName i ++ '\'' : d
saveVariable (Vbl i vc After)       = idName i ++ "\'"
saveVariable (Vbl i vc _)           = idName i 
\end{code}

\subsection{Load Variable}

The Identifier datatype, enforced by \h{validIdent} includes decorations, 
like dashes and dollars,
and can also have symbols and trailing spaces.
\begin{code}
validVarRoot (c:rest)
  | isAlpha c  =  all validVarChar rest
validVarRoot _ = False
validVarChar '_' = True
validVarChar c  =  isAlphaNum c
\end{code}

For UTP variables we need to tighten this up a bit.

Here, for now, we simply make observation variables,
and let post-processing sort things out.
\begin{code}
loadVariable :: MonadFail mf => String -> mf Variable
loadVariable ('\'' : string)
    | validVarRoot string  =  return $ Vbl (jId string) ObsV Before
loadVariable string
  | validVarRoot name
    = case post of
       ("\'")    ->  return $ Vbl ident ObsV After
       ('\'':d)  ->  return $ Vbl ident ObsV $ During d
       _         ->  return $ Vbl ident ObsV Static
  where 
    (name,post) = break (=='\'') string
    ident = jId name
loadVariable string = fail ("loadVariable: invalid variable - "++string)
\end{code}



\newpage
\section{Lexical Basics}

We limit everything to the ASCII subset,
simply because UTF8 Unicode is a mess
(and it's the nicest one!).

\subsection{Tokens}

We have the following token classes:
\begin{description}
  \item [Numbers]~
    Just integers for now,
    with a minus-sign to start if negative,
    with no whitespace between it and the one or more (decimal) digits.
  \item [Identifiers]~
    These start with an alpha, 
    and can follow with alpha, numeric, and underscore
    (\h{Lexbase.validIdent} is too liberal).
    with added decoration for UTP variable classification.
    \textbf{Keywords} form a subset of these.
    We expect identifiers to have one of the following concrete forms:
      \textsf{ident}%
    , \texttt{?}\textsf{ident}%
    , \textsf{ident}\texttt{?}%
    , \textsf{ident}\texttt{?}\textsf{alphas}.
  \item [Delimiters]~
    Small tokens used for general punctuation,
    further classified into: matched (Open/Close) bracketing; and separators.
  \item [Symbols]~
    Tokens assembled from everything else,
    provided they satisfy \texttt{LexBase.validIdent}.
\end{description}
We shall use the dash/prime character as a decoration to indicate variable temporality.
\begin{code}
beforeChar = '\'' -- backquote is visually disruptive
afterChar = '\''
lstvChar = '$'
\end{code}

\begin{tabular}{|l|c|l|}
\hline
  Temp. & Math. & Script 
\\\hline
  Static & $v$ & \texttt{v}
\\\hline
  Before & $v$ & \verb"'v"
\\\hline
  During & $v_m$ & \verb"v'm"
\\\hline
  After & $v'$ & \verb"v'"
\\\hline
\end{tabular}

If any of the above is immediately followed by `\$',
then it denotes the corresponding list-variable.

\subsection{Token Data Type}

\begin{code}
data Token
  =  TNum   Integer
  |  TId    Identifier VarWhen
  |  TLVar  Identifier VarWhen  -- i$
  |  TOpen  String
  |  TClose String
  |  TSep   String
  |  TSym   Identifier
  |  TErr   String
  deriving (Eq,Show)
\end{code}

We provide some rendering code, mostly for error reporting:
\begin{code}
renderToken :: Token -> String
renderToken (TNum i) = show i
renderToken (TId i Static) = idName i
renderToken (TId i Before) = beforeChar : idName i
renderToken (TId i (During d)) = idName i ++ afterChar : d
renderToken (TId i After) = idName i ++ [afterChar]
renderToken (TOpen str) = str
renderToken (TClose str) = str
renderToken (TSep str) = str
renderToken (TSym i) = idName i
renderToken (TErr str) = str

-- useful for lists
renderToken' tok = ' ' : renderToken tok
\end{code}


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
  | c `elem` beforeChar : afterChar : openings ++ closings ++ separators
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

mkName tcons str
  = let (root,temp) = extractTemporality str
    in case ident root of
      But msgs  ->  TErr $ unlines' msgs
      Yes i     ->  tcons i temp

mkId str   = mkName TId str

mkLVar str = mkName TLVar str

extractTemporality cs -- non-empty
 | c1 == beforeChar      =  ( tail cs, Before) --  `nm
 | last cs == afterChar  =  ( init cs, After ) --  nm'
 --    nm       nm$    nm'$    nm'subscr    nm'subscr$
 --     v        v      v         v             v
 --   (nm,S) (nm$,S) (nm$,A) (nm,D subscr) (nm$,D subscr)
 | null rest = ( cs, Static )  -- nm ,  nm$
 | last subscr == lstvChar && null (init subscr)   -- nm'$
                         =  ( root++[lstvChar], After) 
 | have root && have subscr && all isAlphaNum subscr -- nm'subscr
                         =  ( root,    During subscr )
 | have root && have subscr && last subscr == lstvChar  -- nm'subscr$
                         =  ( root++[lstvChar], During $ init subscr )
 | otherwise = ( cs, Static )
 where
    c1 = head cs
    (root,rest) = break (== afterChar) cs
    have [] = False ; have _ = True
    subscr = ttail rest
 

-- tail recursion often requires reversal at end of accumulated lists
mkMys  =  mkSym . reverse   ;   mkDi   =  mkId . reverse
mkRavL = mkLVar . reverse
\end{code}

\subsection{Law Name Reader}

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

\newpage 
\subsection{Lexer}
Now we define the lexer:
\begin{code}
tlex :: String -> [Token]
tlex "" = []
tlex str@(c:cs)
  | isSpace c            =  tlex cs
  | isDigit c            =  tlexNum [c] cs
  | c == '-'             =  tlexMinus cs
  | isAlpha c            =  tlexId False [c] cs
  | c == beforeChar      =  tlexId True  [c] cs
  | c `elem` openings    =  TOpen [c]  : tlex cs
  | c `elem` closings    =  TClose [c] : tlex cs
  | c `elem` separators  =  TSep [c]   : tlex cs
  | otherwise            =  tlexSym [c] cs
\end{code}


Seen one or more digits, keep looking for more.
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

A \texttt{afterChar} may end an identifier,
or indicate that we expect a During subscript,
provided none exists at the start.
Otherwise it is an error.
Also a subscript appearing when a \texttt{afterChar} is already present
is an error.


\begin{code}
-- tlexId isBefore di rest-of-ident
-- note, the di component is never empty when this is called
tlexId _ di ""     =  [ mkDi di ] -- std-var
tlexId _ di [c] 
  | c == lstvChar  =  [ mkRavL di ] -- lst-var
tlexId hasDC di str@(c:cs)
  | isAlpha c  =  tlexId hasDC (c:di) cs
  | isDigit c  =  tlexId hasDC (c:di) cs
  | c == afterChar
      = if hasDC then (derr c di) : tlex cs
                 else  tlexDuring (c:di) [] cs
  | c == kLstVar = mkRavL di : tlex cs 
  | otherwise  =  mkDi di : tlex str
  where
    derr c di = TErr ("Overdecorated: " ++ reverse (c:di))

-- here we accept alphanumeric subscripts
tlexDuring di ""  ""   =  [ mkDi di ]
tlexDuring di ""  [c]
  | c == lstvChar      =  [ mkRavL di ]
tlexDuring di bus ""   =  [ mkId (reverse di ++ reverse bus) ]
tlexDuring di bus [c]  
  | c == lstvChar      =  [ mkRavL (reverse di ++ reverse bus) ]
tlexDuring di bus str@(c:cs)
  | c == kLstVar  =  mkLVar (reverse di ++ reverse bus) : tlex cs
  | isAlpha c  =  tlexDuring di (c:bus) cs
  | isDigit c  =  tlexDuring di (c:bus) cs
  | otherwise  =  mkId (reverse di ++ reverse bus) : tlex str
\end{code}

If none of the above apply, we gobble up a maximum-munch symbol:
\begin{code}
tlexSym mys ""  = [ mkMys mys ]
tlexSym mys str@(c:cs)
  | issymbol c  =  tlexSym (c:mys) cs
  | otherwise  =  mkMys mys : tlex str
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
tread str 
  = case loadTerm str of
      Yes (term,tokens) 
        | null tokens -> putStrLn $ trTerm 0 term
        | otherwise   -> putStrLn ( "tokens leftover: " ++
                                     concat (map renderToken' tokens) )
      But msgs -> putStrLn $ unlines' msgs
\end{code}


\section{Useful Writers}

\begin{code}
saveIndentedNameList  :: Int -> Int -> [String] -> String
saveIndentedNameList ind width names
  = let widths = map length names
        actualwidth = width - ind
        partitions = sizepack actualwidth $ zip names widths
        indent = replicate ind ' '
    in unlines' $ map ((indent++) . intercalate " ") partitions

sizepack :: Int -> [(a,Int)] -> [[a]]
-- packed = sizepack w xws ==> max (map (sum . map snd) xws) <= w
sizepack wall [] = []
sizepack wall xws
  = let (xs,xws') = packfst wall 0 [] xws
    in xs : sizepack wall xws'

packfst :: Int -> Int -> [a] -> [(a,Int)] -> ([a],[(a,Int)])
packfst wall _ xs [] = (reverse xs,[])
packfst wall wsofar accum xws@((x,w):xws')
  |  wnext <= wall  =  packfst wall wnext (x:accum) xws' 
  |  otherwise      =  (reverse accum,xws)
  where
    wnext = wsofar + w
\end{code}