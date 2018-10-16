\section{Test Rendering}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TestRendering (
   trId
 , trVar, trLVar, trGVar
 , trVSet, trOVSet, trVList, trVariableSet
 , trType
 , trValue
 , trTerm
 , trTermZip
 , trSideCond
 , trVarMatchRole, trLstVarMatchRole, trVarTable
 , trBinding
 , seeV, seeLV, seeGV, seeVL, seeVS
 , seeType, seeVal, seeTerm, seeBind, seeVarTable
 , seeTerms, seeBinds
) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList,assocs)
import qualified Data.Set as S
import Data.List (nub, sort, (\\), intercalate)
import Data.Char

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Binding
import Matching
import TermZipper
\end{code}

\subsection{Test Rendering Intro.}

We provide a simple, almost certainly un-parsable,
rendering of datatypes to ease debugging.

\newpage
\subsection{Variables}

\begin{code}
trId :: Identifier -> String
trId (Identifier s)  =  s

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
trVW Before s      =  '`':s
trVW (During m) s  =  s++'_':m
trVW After s       =  s++"'"
trVW Textual s     =  s++"\""

trVar :: Variable -> String
trVar (Vbl i vc vw) = trVW vw $ trVCf vc $ trId i

trLVar :: ListVar -> String
trLVar (LVbl (Vbl i vc vw) is js)
 = trVW vw (trVCf vc $ trLId i) ++ trLess is js

trLId i = concat $ map dia_line $ trId i
trLess [] []  =  ""
trLess is js  =  '\\' : ( intercalate "," ( map trId is ++ map trLId js ) )

trGVar :: GenVar -> String
trGVar (StdVar v)   =  trVar v
trGVar (LstVar lv)  =  trLVar lv
\end{code}

\subsection{Types}

\begin{code}
trType :: Type -> String
trType ArbType            =  _tau
trType (TypeVar i)        =  trId i
trType (TypeApp i ts)     =  trId i ++ "(" ++ trTypes ts ++ ")"
trType (DataType i itss)  =  "ADT"
trType (FunType ta tr)    =  "("++ trType ta ++ spaced _fun ++ trType tr ++ ")"
trType (GivenType i)      =  trId i

trTypes = seplist " " trType

seplist sep tr = intercalate sep . map tr
\end{code}

\newpage
\subsection{Terms}

Kinds and Values:
\begin{code}
trTK :: TermKind -> String
trTK _ = "" -- ignore for now
-- trTK P = "!"
-- trTK (E t) = trType t

trValue :: Value -> String
trValue (Boolean False)  =  "ff"
trValue (Boolean True)   =  "tt"
trValue (Integer i)      =  show i
trValue (Txt s)          =  show s
\end{code}


\textbf{Before we proceed, we need a table/function that returns
the precedence level of a \texttt{Cons} identifier.
For now, let's hard-code one.
Suggested Precedence Table:}
$$
        =        \;\mapsto  1
\qquad  \equiv   \;\mapsto  2
\qquad  \implies \;\mapsto  3
\qquad  \lor     \;\mapsto  4
\qquad  \land    \;\mapsto  5
\qquad  \lnot    \;\mapsto  6
$$
We might also want to fine tune rendering modes,
especially in live proofs:

\begin{tabular}{|c|c|c|}
\hline
   render-mode & $\equiv$[P,$\equiv$[Q,R]] & $\equiv$[P,Q,R]
\\\hline
   assoc       & $P \equiv Q \equiv R$     & $P \equiv Q \equiv R$
\\\hline
   non-assoc  & $P \equiv (Q \equiv R)$    & $P \equiv Q \equiv R$
\\\hline
   forced-l  & $P \equiv (Q \equiv R)$    & $(P \equiv Q) \equiv R$
\\ forced-r  & $P \equiv (Q \equiv R)$    & $P \equiv (Q \equiv R)$
\\\hline
\end{tabular}
~
Based on experience with live-proof we can now say that
we use ``non-assoc'' render mode for all associative operators.
\begin{code}
type InfixKind = ( Int     -- precedence
                 , Bool )  -- true if *syntactically* associative
prc :: Identifier -> InfixKind
prc (Identifier n)
  | n == "="       =  (1,False)
  | n == _equiv    =  (2,False)
  | n == _implies  =  (3,False)
  | n == _lor      =  (4,False) -- force parenthesis for nested 'or'
  | n == _land     =  (5,False) -- force parenthesis for nested 'and'
  | n == _lnot     =  (6,False)
  | otherwise      =  (0,False) -- force parenthesising if not at top-level
\end{code}

Rather than rendering zippers on the fly,
we mark the focus and un-zip,
and ensure that the term renderer checks for a marked term.
\begin{code}
markfocus :: Term -> Term
markfocus t = Cons P focusMark [t]

focusMark = fromJust $ ident "__focus__"

highlightFocus = magenta
\end{code}

We use a precedence arument when rendering terms.
\begin{code}
trTerm :: Int -> Term -> String -- 1st arg is precedence
\end{code}

First, atomic terms
\begin{code}
trTerm p (Val tk k)           =  trValue k
trTerm p (Var tk v)           =  trVar v
trTerm p (Type t)             =  trType t
\end{code}

A \texttt{Cons}-node with one subterm
may need special handling:
a marked focus term needs highlighting;
it might be universal closure ($[\_]$);
or an application of name $nm$ (symbol $\lhd$)
to an atomic argument $a$ that has no parentheses: $nm~a$ ($\lhd a$).
\begin{code}
trTerm ctxtp (Cons tk s [t])
 | s == focusMark    =  highlightFocus $ trTerm ctxtp t
 | idName s == "[]"  =  "["++trTerm 0 t++"]"
 | isAtomic t        =  trAtomic s $ trTerm 0 t
 where
   trAtomic s r
    | isSymbId s  =  trId s ++ r
    | otherwise   =  trId s ++ ' ':r
\end{code}

Rendering an infix operator with two or more arguments.
We ensure that sub-terms are rendered with the infix operator precedence
as their context precedence.
\begin{code}
trTerm ctxtp (Cons tk opn ts@(_:_:_))
 | isSymbId opn  =  trBracketIf (opp < ctxtp || opp == ctxtp && not assoc)
                         $ intercalate (trId opn) $ map (trTerm opp) ts
 where prcs@(opp,assoc) = prc opn
\end{code}

In all other cases we simply use classical function application notation
$f(e_1,e_2,\dots,e_n)$.
\begin{code}
trTerm _ (Cons tk n ts)
  =  trId n ++ trContainer ( "(", ",", ")" ) ts
\end{code}

Binders and substitution are straightforward (for now).
\begin{code}
trTerm p (Bind tk n vs t)     =  trAbs p tk n (S.toList vs) t
trTerm p (Lam tk n vl t)      =  trAbs p tk n vl            t
trTerm p (Sub tk t sub)       =  trTerm p t ++ trSub p sub
\end{code}

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
trTerm _ (Iter tk na ni lvs@(_:_:_))
 | isSymbId ni  = silentId na ++ "(" ++ seplist (trId ni) trLVar lvs ++ ")"
 where silentId na@(Identifier i)
  -- logical-and is the 'default' for na, so we keep it 'silent'
        | i == _land  =  ""
        | otherwise   =  trId na

trTerm _ (Iter tk na ni lvs)
  =  trId na ++ "{" ++ trId ni ++ "(" ++ seplist "," trLVar lvs ++ ")}"
\end{code}


General way to render a named, bracketed and separated ``container''.
\begin{code}
trContainer (lbr,sep,rbr) ts
  = lbr ++ intercalate sep (map (trTerm 0) ts) ++ rbr
\end{code}

\begin{code}
trSub ctxtp (Substn tsub lvsub)
 = "[" ++
       (trTL ctxtp "," rts  `mrg` trVL (map LstVar rlvs)) ++
   "/" ++
       trVL (map StdVar tvs ++ map LstVar tlvs) ++
   "]"
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

trApply p n (lbr,sep,rbr) ts  =  lbr ++ trTL p sep ts ++ rbr

trTL p sep ts = seplist sep (trTerm p) ts

trAbs p tk n vl t
 = "("++trId n ++ ' ':trVL vl ++ spaced _bullet ++ trTerm p t ++ ")"

trVL = seplist "," trGVar

trVList vl  =  _langle ++ trVL vl ++ _rangle
trVSet vs   =  "{" ++ trOVSet vs ++ "}"
trOVSet vs  =  trVL (S.toList vs)

trVariableSet vs = "{" ++ trVariableL (S.toList vs) ++ "}"
trVariableL = seplist "," trVar
\end{code}

\subsection{Term Zipper}

We mark the focus, exit the zipper, and render as normal.
\begin{code}
trTermZip (t,wayup) = trTerm 0 $ exitTZ (markfocus t,wayup)
\end{code}

\subsection{Side Conditions}

\begin{code}
trSideCond (SC vs vscmap)
 = intcalNN ";" (trFresh vs : trVarSCMap vscmap)

trFresh vs
 | S.null vs  =  ""
 | otherwise  =  "fresh"++ trVSet vs

trVarSCMap vscmap = map trVarSideCond $ M.assocs vscmap
trVarSideCond (v,(Exact vs)) = trOVSet vs ++ "=" ++ trVar v
trVarSideCond (v,(Approx pre mD mC))
 = intcalNN ";" [trPre pre,trD mD,trC mC]
 where
   trPre True = "pre:"++trVar v ; trPre False = ""
   trD Nothing = ""
   trD (Just vs) = trOVSet vs ++ _notin ++ trVar v
   trC Nothing = ""
   trC (Just vs) = trOVSet vs ++ _supseteq ++ trVar v
\end{code}

\newpage
\subsection{Variable Data}

\begin{code}
trVarMatchRole :: VarMatchRole -> String
trVarMatchRole (KnownConst t)  =  spaced _triangleq ++ trTerm 0 t
trVarMatchRole (KnownVar t)    =  " : " ++ trType t
trVarMatchRole UnknownVar      =  " ?"
\end{code}

\begin{code}
trLstVarMatchRole :: LstVarMatchRole -> String
trLstVarMatchRole (KnownVarList vl _ _)
  =  spaced _triangleq ++ trVList vl
trLstVarMatchRole (KnownVarSet  vs _ _)
  =  spaced _triangleq ++ trVSet vs
trLstVarMatchRole UnknownListVar     =  " ?"
\end{code}

\begin{code}
trVarTable :: VarTable -> String
trVarTable vt
 = case lns of
     []  ->  "Known Variables: None"
     _   ->  "Known Variables:\n"
             ++ unlines' lns
 where lns = (    map trVTVV (vtList vt)
               ++ map trVTLV (stList vt)
               ++ map trVTLV (dtList vt)
              )

trVTVV (v,vmr)   =  trVar v ++ trVarMatchRole    vmr

trVTLV (v,lvmr)  =  trVar v ++ trLstVarMatchRole lvmr
\end{code}

\newpage
\subsection{Bindings}

\begin{code}
trVarBind (BindVar v) = trVar v
trVarBind (BindTerm t) = trTerm 0 t
trVarBind vb = _ll ++ show vb ++ _gg

trLstVarBind (BindList vl)  =  _langle ++ trVL vl ++ _rangle
trLstVarBind (BindSet vs)  =  "{" ++ trVL (S.toList vs) ++ "}"
trLstVarBind (BindTerms ts)  =  _langle ++ trTL 0 ", " ts ++ _rangle
\end{code}

\begin{code}
trBinding :: Binding -> String
trBinding = trBinding' . dumpBinding

trBinding' (vb,sb,lb)
 = "{ " ++ seplist "," id (map trVB vb ++ map trSB sb ++ map trLB lb)
        ++ " }"

trAssoc tr pairs = "{ " ++ seplist ", " tr pairs ++ " }"

trVB ((i,vc),vb)
 = trVC vc (trId i) ++ spaced _maplet ++ trVarBind vb

trSB (s,t) = s ++ spaced _maplet ++ t

trLB ((i,vc,is,js),lvb)
  = trVC vc (trId i) ++
    "$" ++
    (if nowt then "" else "\\") ++
    (if noIs then "" else seplist "," trId is) ++
    (if noJs then "" else ";" ++ seplist "," trId js) ++
    ")"
    ++
    spaced _maplet ++ trLstVarBind lvb
  where
    noIs = null is
    noJs = null js
    nowt = noIs && noJs
\end{code}

Seeing them in all their glory:
\begin{code}
seeV = putStrLn . trVar
seeLV = putStrLn . trLVar
seeGV = putStrLn . trGVar
seeVL = putStrLn . trVList
seeVS = putStrLn . trVSet
seeType = putStrLn . trType
seeVal = putStrLn . trValue
seeTerm t = putStrLn $ trTerm 0 t
seeBind = putStrLn . trBinding
seeVarTable = putStrLn . trVarTable

seeMany see []      =  return ()
seeMany see [x]     =  see x
seeMany see (x:xs)  =  do see x
                          putStrLn "--"
                          seeMany see xs

seeTerms = seeMany seeTerm
seeBinds = seeMany seeBind
\end{code}
