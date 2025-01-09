\chapter{Test Rendering}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017--2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TestRendering (
   trId, trIdU
 , trVar, trVarU, trLVar, trLVarU, trGVar, trGVarU
 , trVSet, trVSetU, trOVSet, trOVSetU
 , trVList, trVListU, trVariableSet, trVariableSetU
 , trMap
 , trType
 , trValue
 , trTerm, trTermU
 , trSub, trSubU
 , trTermZip, trTermZipU
 , trSideCond, trSideCondU
 , trAsn, trAsnU, trNmdAsn, trNmdAsnU
 , truelawname, (-.-), nicelawname
 , trVarMatchRole, trVarMatchRoleU
 , trLstVarMatchRole, trLstVarMatchRoleU
 , trVarTable, trVarTableU
 , trLstLVarOrTerm, trLstLVarOrTermU
 , trBinding, trBindingU
 , seplist
 , seeV, seeLV, seeGV, seeVL, seeVS
 , seeType, seeVal, seeTerm, seeBind, seeVarTable
 , seeTerms, seeBinds
) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList,assocs,lookup)
import qualified Data.Set as S
import Data.List (nub, sort, (\\), intercalate)
import Data.List.Split (splitOn)
import Data.Char

import NotApplicable
import Symbols
import Utilities
import UnivSets
import LexBase
import Variables
import AST
import SideCond
import Assertions
import VarData
import Binding
import Matching
import TermZipper

import Debugger
\end{code}

\section{Test Rendering Intro.}

We provide a simple, almost certainly un-parsable,
rendering of datatypes to ease debugging.

We support one way of viewing identifiers,
which basically shows the number component if non-zero,
and hides it otherwise.

one (\texttt{trXXX}) that hides the ``unique number'' component,
and another (\texttt{trXXXU}) that displays it.

\newpage
\section{Variables}

\begin{code}
trId :: Identifier -> String
trId (Identifier s u)  
  | u == 0     =  widthHack 2 $ nicesym s
  | otherwise  =  widthHack 2 $ (nicesym s ++ _subNum u)

trIdU :: Identifier -> String
trIdU (Identifier s u)  =  widthHack 2 $ (nicesym s ++ _subNum u)

-- can't handle nesting of bold, underline and colours right now...
trVC :: VarClass -> String -> String
trVC ObsV   =  id
trVC ExprV  =  id -- underline? bold?
trVC PredV  =  id -- underline? bold

trVCf :: VarClass -> String -> String
trVCf ObsV s = s
trVCf _ s = s -- bold s - currently can't nest these effects.

trVW :: VarWhen -> String -> String
trVW Static s      =  s
trVW Before s      =  s  -- '`':s
trVW (During m) s  =  s++'_':m
trVW After s       =  s++"'"
trVW Textual s     =  s++"\""

trVar :: Variable -> String
trVar = trvar trId
trVarU = trvar trIdU

trvar trid (Vbl i vc vw) = trVW vw $ trVCf vc $ trId i

trLVar = trlvar trId
trLVarU = trlvar trIdU

trlvar trid (LVbl (Vbl i vc vw) is js)
 = trVW vw (trVCf vc $ trlid trid i) ++ trless trid is js

trlid trid i = trid i ++ "$" -- concat $ map dia_line $ trid i
trless trid [] []  =  ""
trless trid is js  =  '\\' : ( intercalate "," ( map trid is ++
                                                 map (trlid trid) js ) )

trGVar = trgvar trId
trGVarU = trgvar trIdU

trgvar trid (StdVar v)   =  trvar trid v
trgvar trid (LstVar lv)  =  trlvar trid lv
\end{code}

\section{Types}

\begin{code}
trType :: Type -> String
trType ArbType           =  _tau
trType (TypeVar i)       =  trId i
trType (TypeCons (Identifier i _) [t])
  | i == "P"             =  "\x2119 "
                            ++ (trBracketIf (not $ isAtmType t) (trType t)) 
  | i == "*"             =  (trBracketIf (not $ isAtmType t) (trType t)) 
                             ++ "\x002a "
trType (TypeCons i [t])  =  trId i ++ " " ++ trType t
trType (TypeCons i ts)   =  trId i ++ "(" ++ trTypes ts ++ ")"
trType (AlgType i itss)  =  "ADT"
-- fun-types are right-associative
trType (FunType ft@(FunType _ _) tr)   
  =  "(" ++ trType ft ++ ")" ++ spacep _fun ++ trType tr
trType (FunType ta tr)   =  trType ta ++ spacep _fun ++ trType tr
trType (GivenType (Identifier i _)) 
  -- hack - should be done in Symbols
  | i == "B"  =  " \x1d539 "
  | i == "N"  =  "\x2115"
  | i == "Z"  =  "\x2124"
  | i == "Q"  =  "\x211a"
  | i == "R"  =  "\x211d"
  | i == "C"  =  "\x2102"
  | i == "P"  =  "\x2119"
  | i == "*"  =  "\x002a"
trType (GivenType i)      =  trId i

trType BottomType = _bot

trTypes = seplist " " trType

seplist :: [a] -> (b -> [a]) -> [b] -> [a]
seplist sep tr = intercalate sep . map tr
\end{code}

\section{Terms}

\subsection{Kinds and Values}

\begin{code}
trTK :: Type -> String
trTK _ = "" -- ignore for now
-- trTK P = "!"
-- trTK (E t) = trType t

trValue :: Value -> String
trValue (Boolean False)  =  nicesym "false"
trValue (Boolean True)   =  nicesym "true"
trValue (Integer i)      =  show i
\end{code}

\subsection{Operator Fixity and Precedence}

He we follow the Haskell convention of associating 
a \emph{fixity}
(None,Left,Right) and a prededence ($p > 0$) with an infix operator.


\begin{code}
data Fixity 
  = NotAssoc -- not associative
  | LAssoc -- left-assoc
  | RAssoc -- right-assoc
  | MixFix -- ternary mixfix
  | NotInfix -- not an infix operator
  deriving (Eq,Ord,Show)

type OpKind = ( Int, Fixity )   -- precedence
\end{code}

Based on experience with live-proof we can now say that
we use ``non-assoc'' render mode for all associative operators.

\newpage
Suggested Precedence Table:
\begin{code}
precTable
 = M.fromList
    [ ( ";"        , (1,LAssoc))
    , ( ":="       , (1,NotAssoc))
    , ( "refines"  , (1,LAssoc))
    , ( "vdash"    , (2,LAssoc))
    , ( "eqv"      , (3,LAssoc))
    , ( "sqcap"    , (4,LAssoc))
    , ( "imp"      , (4,LAssoc))
    , ( "while"    , (4,LAssoc)) 
    , ( "or"       , (5,LAssoc)) 
    , ( "and"      , (6,LAssoc)) 
    , ( "cons"     , (7,RAssoc))
    , ( "cat"      , (7,RAssoc))
    , ( "="        , (7,NotAssoc))
    , ( "pfx"      , (7,NotAssoc))
    , ( "mbr"      , (7,NotAssoc))
    , ( "subseteq" , (7,NotAssoc))
    , ( "until"    , (8,NotAssoc))
    , ( "wait"     , (8,NotAssoc))
    , ( "+"        , (8,LAssoc))
    , ( "union"    , (8,LAssoc))
    , ( "-"        , (8,NotAssoc))
    , ( "\\"       , (9,NotAssoc))
    , ( "*"        , (9,LAssoc))
    , ( "intsct"   , (9,LAssoc))
    , ( "div"      , (9,NotAssoc))
    , ( "mod"      , (9,NotAssoc))
    ]
opkind :: String -> OpKind
opkind n
  = case M.lookup n precTable of
     Nothing  ->  (-1,NotInfix)
     Just ik  ->  ik
\end{code}

\subsection{Focus Marking}

Rather than rendering zippers on the fly,
we mark the focus and un-zip,
and ensure that the term renderer checks for a marked term.
\begin{code}
markfocus :: Term -> Term
markfocus t = Cons arbpred True focusMark [t]

focusMark = fromJust $ ident "__focus__"

highlightFocus = magenta
\end{code}

\subsection{Rendering Terms}

We use a precedence argument when rendering terms.
\begin{code}
trTerm  :: Int -> Term -> String -- 1st arg is precedence
trTerm = trterm trId
trTermU :: Int -> Term -> String
trTermU = trterm trIdU
trterm :: (Identifier -> String) -> Int -> Term -> String
\end{code}

\subsubsection{Atomic Terms}

\begin{code}
trterm trid p (Val tk k)           =  trValue k
trterm trid p (Var tk v)           =  trVar v
trterm trid p (Typ t)              =  trType t
\end{code}

\subsubsection{Rendering Binders and Substitution}

Binders and substitution are straightforward:
\begin{code}
trterm trid p (Bnd tk n vs t)  =  trabs trid p tk n (S.toList vs) t
trterm trid p (Lam tk n vl t)  =  trabs trid p tk n vl            t
-- give assignment special treatment
trterm trid p (Sub tk (Var _ (Vbl (Identifier ":=" _) _ _)) sub)
  =  trasg trid sub
trterm trid p (Sub tk t sub)
  | isAtomic t  =       trterm trid p t      ++ trsub trid p sub
  | otherwise   =  "("++trterm trid 0 t++")" ++ trsub trid p sub
\end{code}

\subsubsection{Rendering Closure}

A closure expects the identifier to be of the form leftbracket\_rightbracket
\begin{code}
trterm trid p (Cls n t)
  =  nicesym lbr ++ trterm trid 0 t ++ nicesym rbr
  where (lbr,rbr) = splitClosureId n
\end{code}

\subsubsection{Rendering Iterated Constructions}

For an iterated construct with listings-variable list of length $n$,
we have three cases:

\begin{tabular}{|c|c|c|c|}
  \hline
  na & ni & $n>1$ & rendering
\\\hline
  $\land$ & $\oplus$ & yes & $(v_1\oplus v_2\oplus\dots\oplus v_n)$
\\\hline
  $\bigotimes$ & $\oplus$ & yes
  & $\bigotimes(v_1\oplus v_2\oplus\dots\oplus v_n)$
\\\hline
  $nm$, $\bigotimes$ & $\oplus$ &
  & $nm\{(v_1\oplus v_2\oplus\dots\oplus v_n)\}$
\\\hline
\end{tabular}
~

\begin{code}
trterm trid _ (Iter tk _ na _ ni lvs@(_:_:_))
 | isSymbId ni  = silentId na ++ "(" ++ seplist (trid ni) (trlvar trid) lvs ++ ")"
 where silentId na@(Identifier i _)
  -- logical-and is the 'default' for na, so we keep it 'silent'
        | i == "land"  =  ""
        | i == "and"   =  ""
        | otherwise    =  trid na

trterm trid _ (Iter tk _ na _ ni lvs)
  =  trid na ++ "{" ++ trid ni ++ "(" ++ seplist "," (trlvar trid) lvs ++ ")}"
\end{code}

\subsubsection{Rendering Constructions}

A \texttt{Cons}-node with one subterm
may need special handling
a marked focus term needs highlighting:
\begin{code}
trterm trid ctxtp (Cons tk _ s [t])
 | s == focusMark  =  highlightFocus $ trterm trid ctxtp t
 | s == jId "not"  =  trnot s t
 | s == jId "neg"  =  trunary s t
 where  
  trnot s t
    | isAtomic t  =  trid s ++ trterm trid 99 t    
    | otherwise   =  (trid s)++"("++trterm trid 0 t++")"
  trunary s t
    | isAtomic t  =  '(':(trid s)++trterm trid 0 t++")"
    | otherwise   =  trid s ++ trterm trid 99 t
\end{code}

Rendering an ``infix-like'' ternary operator.
For now the most significant is the conditional ($\cond\_$)
\begin{code}
trterm trid ctxtp (Cons tk _ opn@(Identifier nm _) [p,b,q])
 | nm == "cond"  =  trBracketIf (opp <= ctxtp)
                        (trterm trid opp p
                         ++ trid lif 
                         ++ trterm trid 0 b 
                         ++ trid rif
                         ++ trterm trid opp q)
 where
   lif = jId "lif" ; rif = jId "rif"
   prcs@(opp,fixity) = opkind nm
   isMix3 = fixity == MixFix
\end{code}

Rendering an infix operator with exactly two arguments.
We ensure that sub-terms are rendered with the infix operator precedence
as their context precedence.
\begin{code}
trterm trid ctxtp (Cons tk _ opn@(Identifier nm _) ts@[t1,t2])
 | isOp  =  trBracketIf (opp <= ctxtp)
              ( trterm trid opp t1
                ++ " " ++ trId opn ++ " "
                ++ trterm trid opp t2 )
 where
   prcs@(opp,fixity) = opkind nm
   isOp = fixity /= NotInfix
\end{code}

Rendering a left-infix operator when the first sub-term uses the same operator
$$op(\seqof{op(es)}\cat fs) = op(es\cat fs)$$
\begin{code}
trterm trid ctxtp (Cons tk sub opn@(Identifier nm _) 
                  (Cons _ _ opn' ts':ts))
 | isLFix && opn == opn'  =  trterm trid ctxtp $ Cons tk sub opn (ts'++ts)
 where
   prcs@(opp,fixity) = opkind nm
   isLFix = fixity == LAssoc
\end{code}

Rendering a right-infix operator when the last sub-term uses the same operator
$$op(es \cat \seqof{op(fs)}) = op(es\cat fs)$$
\begin{code}
trterm trid ctxtp (Cons tk sub opn@(Identifier nm _) ts@(_:_:_))
 | isRFix
   = case tE of
       (Cons _ _ opn' ts') | opn == opn'  
          ->  trterm trid ctxtp $ Cons tk sub opn (tsI++ts')
       _  ->  trBracketIf (opp <= ctxtp)
                  $ intercalate (trId opn) 
                  $ map (trterm trid opp) ts
 where
   prcs@(opp,fixity)  =  opkind nm
   isRFix             =  fixity == RAssoc
   (tsI,tE)           =  splitAtEnd ts
   splitAtEnd [x,y] = ([x],y)
   splitAtEnd (x:xs) 
     =  let (xs',y) = splitAtEnd xs
        in (x:xs',y)
\end{code}

Rendering an infix operator with two or more arguments.
We ensure that sub-terms are rendered with the infix operator precedence
as their context precedence.
\begin{code}
trterm trid ctxtp (Cons tk _ opn@(Identifier nm _) ts@(_:_:_))
 | isOp  =  trBracketIf (opp <= ctxtp)
                        $ intercalate (trId opn) 
                        $ map (trterm trid opp) ts
 where
   prcs@(opp,fixity) = opkind nm
   isOp = fixity /= NotInfix
\end{code}

We have some containers such as sets, lists and UTCP roots:
\begin{code}
trterm trid _ (Cons tk _ n ts)
  | n == jId "set"  =  trcontainer trid ( "{", ",", "}" ) ts
  | n == jId "seq"  =  trcontainer trid ( "[", ",", "]" ) ts
  | n == jId "r"    =  "r"++concat (map trRoot ts)
  where 
    trRoot (Val _ (Integer i)) = show i
    trRoot (Val _ (Boolean b)) = if b then "!" else ""
    trRoot _ = ""
\end{code}

In all other cases we simply use classical function application notation
$f(e_1,e_2,\dots,e_n)$.
\begin{code}
trterm trid _ (Cons tk _ n ts)
  =  trId n ++ trcontainer trid ( "(", ",", ")" ) ts
\end{code}

\subsubsection{Term Rendering Helpers}


General way to render a named, bracketed and separated ``container''.
\begin{code}
trcontainer trid (lbr,sep,rbr) ts
  = lbr ++ intercalate sep (map (trterm trid 0) ts) ++ rbr
\end{code}

Substitution (and assignment!)
\begin{code}
trSub = trsub trId
trSubU = trsub trIdU

trsub trid ctxtp (Substn tsub lvsub)
 = "[" ++
       (trtl trid ctxtp "," rts  `mrg` trvl trid (map LstVar rlvs)) ++
   "/" ++
       trvl trid (map StdVar tvs ++ map LstVar tlvs) ++
   "]"
 where
  (tvs,rts) = unzip $ S.toList tsub
  (tlvs,rlvs)  =  unzip $ S.toList lvsub
  mrg ""  ""   =  ""
  mrg cs  ""   =  cs
  mrg ""  cs   =  cs
  mrg cs1 cs2  =  cs1 ++ ',':cs2

trasg trid (Substn tsub lvsub)
  = "(" ++
        trvl trid (map StdVar tvs ++ map LstVar tlvs) ++
    " := " ++
        (trtl trid 0 "," rts  `mrg` trvl trid (map LstVar rlvs)) ++
    ")"
  where
   (tvs,rts) = unzip $ S.toList tsub
   (tlvs,rlvs)  =  unzip $ S.toList lvsub
   mrg ""  ""   =  ""
   mrg cs  ""   =  cs
   mrg ""  cs   =  cs
   mrg cs1 cs2  =  cs1 ++ ',':cs2
\end{code}

These will eventually do some sort of multi-line pretty-printing.
\begin{code}
trBracketIf True  s  =  "("++s++")"
trBracketIf False s  =  s

trapply trid p n (lbr,sep,rbr) ts  =  lbr ++ trtl trid p sep ts ++ rbr

trtl trid p sep ts = seplist sep (trterm trid p) ts

trabs trid p tk n vl t
 = "("++trId n ++ ' ':trvl trid vl ++ spaced _bullet ++ trterm trid p t ++ ")"

trvl trid = seplist "," $ trgvar trid

trVList = trvlist trId
trVListU = trvlist trIdU
trvlist trid vl  =  _langle ++ trvl trid vl ++ _rangle

trVSet = trvset trId
trVSetU = trvset trIdU
trvset trid vs   =  "{" ++ trovset trid vs ++ "}"

trOVSet = trovset trId
trOVSetU = trovset trIdU
trovset trid vs
 | S.null vs  =  _emptyset
 | otherwise  =  trvl trid (S.toList vs)

trVariableSet = trvariableset trId
trVariableSetU = trvariableset trIdU

trvariableset trid vs = "{" ++ trvariablel trid (S.toList vs) ++ "}"
trvariablel trid = seplist "," $ trvar trid

trMap     trK trD m     = "{" ++ trMapLets trK trD (M.assocs m) ++ "}"
trMapLets trK trD kds   = seplist "," (trMapLet trK trD) kds
trMapLet  trK trD (k,d) = trK k ++ " " ++ _maplet ++ "  "++ trD d
\end{code}

\section{Term Zipper}

We mark the focus, exit the zipper, and render as normal.
\begin{code}
trTermZip = trtz trId
trTermZipU = trtz trIdU
trtz trid (t,wayup) = trterm trid 0 $ exitTZ (markfocus t,wayup)
\end{code}

\section{Side Conditions}

\begin{code}
trSideCond = trsidecond trId
trSideCondU = trsidecond trIdU
trsidecond trid sc@(vscs,fvs)
  | isTrivialSC sc  =  _top
  | otherwise       =  intcalNN ", " 
                         ( concat (map (trtvarsidecond trid) vscs)
                           ++ [trfresh trid fvs] )

trtvarsidecond trid (VSC gv NA NA NA) = [_top]
trtvarsidecond trid (VSC gv mvsD mvsC mvsCd)
  = [trDisjSC trid gv mvsD, trCovByM trid gv mvsC, trDynCovM trid gv mvsCd]

trDisjSC trid gv NA = ""
trDisjSC trid gv (The vsD)
  | S.null vsD  =  ""
  | otherwise   =  trovset trid vsD ++ _notin ++ trgvar trid gv

trCovByM trid gv NA = ""
trCovByM trid gv (The vsC) 
  = trovset trid vsC ++ _supseteq ++ trgvar trid gv

trDynCovM trid gv NA = ""
trDynCovM trid gv (The vsC) 
  = trovset trid vsC ++ _supseteq ++_subStr "a" ++ trgvar trid gv


trfresh trid fvs
  | S.null fvs  =  ""
  | otherwise   =  "fresh:" ++ trovset trid fvs
\end{code}

\section{Assertions}

\begin{code}
trAsn = trasn trId
trAsnU = trasn trIdU

trasn trid (Assertion trm ([],_))  =  trterm trid 0 trm
trasn trid (Assertion trm sc)      =  trterm trid 0 trm ++ ", " ++ trSideCond sc

trNmdAsn = trnmdasn trId
trNmdAsnU = trnmdasn trIdU

trnmdasn trid (lawnm,asn) =  truelawname lawnm ++ ": " ++ trasn trid asn

truelawname, nicelawname :: String -> String
truelawname  =  id
nicelawname  =  widthHack 2 . foldl1 (-.-) . map nicesym . splitOn nicesplit
nicesplit = "_"
n1 -.- n2  =  n1 ++ nicesplit ++ n2
\end{code}

\newpage
\section{Variable Data}

\begin{code}
trVarMatchRole :: VarMatchRole -> String
trVarMatchRole = trvmr trId
trVarMatchRoleU = trvmr trIdU

trvmr trid (KnownConst t)  =  spaced _triangleq ++ trterm trid 0 t
trvmr trid (KnownVar t)    =  " : " ++ trType t
trvmr trid UnknownVar      =  " ?"
\end{code}

\begin{code}
trLstVarMatchRole :: LstVarMatchRole -> String
trLstVarMatchRole = trlstvarmatchrole trId
trLstVarMatchRoleU = trlstvarmatchrole trIdU

trlstvarmatchrole trid (KnownVarList vl _ _)
  =  spaced _triangleq ++ trvlist trid vl
trlstvarmatchrole trid (KnownVarSet  vs _ _)
  =  spaced _triangleq ++ trvset trid vs
trlstvarmatchrole trid UnknownListVar     =  " ?"
\end{code}

\begin{code}
trVarTable :: VarTable -> String
trVarTable = trvartable trId
trVarTableU = trvartable trIdU

trvartable trid vt
 = unlines' (   map (trvtvv trid) (vtList vt)
             ++ map (trvtlv trid) (stList vt)
             ++ map (trvtlv trid) (dtList vt)
            )

trvtvv trid (v,vmr)   =  trVar v ++ trvmr trid    vmr

trvtlv trid (v,lvmr)  =  trVar v ++ trLstVarMatchRole lvmr
\end{code}

\newpage
\section{Bindings}

\begin{code}
trvarbind trid (BindVar v) = trVar v
trvarbind trid (BindTerm t) = trterm trid 0 t
trvarbind trid vb = _ll ++ show vb ++ _gg

trlstvarbind trid (BindList vl)
                          =  _langle ++ trvl trid  vl                 ++ _rangle
trlstvarbind trid (BindSet vs)
                          =  "{"     ++ trvl trid (S.toList vs)      ++ "}"
trlstvarbind trid (BindTLVs tlvs)  =  trlstlvarorterm trid tlvs

trLstLVarOrTerm = trlstlvarorterm trId
trLstLVarOrTermU = trlstlvarorterm trIdU
trlstlvarorterm trid lvts = _langle ++ seplist ", " (trtlv trid) lvts ++ _rangle

trtlv trid = either (trlvar trid) (trterm trid 0)
 -- trtlv trid (Left lv)  =  trLVar trid lv
 -- trtlv trid (Right t)  =  trterm trid 0 t
\end{code}

\begin{code}
trBinding = trbinding trId
trBindingU = trbinding trIdU

trbinding trid = trbinding' trid . dumpBinding

trbinding' trid (vb,sb,lb)
 = "{ " ++ seplist ", " id (map (trvb trid) vb ++
                            map (trsb trid) sb ++
                            map (trlb trid) lb)
        ++ " }"

trAssoc tr pairs = "{ " ++ seplist ", " tr pairs ++ " }"

trvb trid ((i,vc),vb)
 = trVC vc (trid i) ++ spaced _maplet ++ trvarbind trid vb

trsb trid (s,t) = s ++ spaced _maplet ++ t

trlb trid ((i,vc,is,js),lvb)
  = trVC vc (trid i) ++
    "$" ++ trless trid is js ++
  --   (if nowt then "" else "\\") ++
  --   (if noIs then "" else seplist "," trid is) ++
  --   (if noJs then "" else ";" ++ seplist "," trid js) ++
    spaced _maplet ++ trlstvarbind trid lvb
  -- where
  --   noIs = null is
  --   noJs = null js
  --   nowt = noIs && noJs
\end{code}

Seeing them in all their glory:
\begin{code}
seeV = putStrLn . trVarU
seeLV = putStrLn . trLVarU
seeGV = putStrLn . trGVarU
seeVL = putStrLn . trVListU
seeVS = putStrLn . trVSetU
seeType = putStrLn . trType
seeVal = putStrLn . trValue
seeTerm t = putStrLn $ trTermU 0 t
seeBind = putStrLn . trBindingU
seeVarTable = putStrLn . trVarTableU

seeMany see []      =  return ()
seeMany see [x]     =  see x
seeMany see (x:xs)  =  do see x
                          putStrLn "--"
                          seeMany see xs

seeTerms = seeMany seeTerm
seeBinds = seeMany seeBind
\end{code}
