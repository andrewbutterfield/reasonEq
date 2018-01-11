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
 , trType
 , trValue, trTerm
 , trVarMatchRole, trLstVarMatchRole, trVarTable
 , trBinding
 , seeV, seeLV, seeGV, seeType, seeVal, seeTerm, seeBind, seeVarTable
 , seeTerms, seeBinds
) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub, sort, (\\), intercalate)

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import VarData
import Binding
import Matching
import MkTestBind
\end{code}

\subsection{Test Rendering Intro.}

We provide a simple, almost certainly un-parsable,
rendering of datatypes to ease debugging.

\newpage
\subsection{Variables}

\begin{code}
trId :: Identifier -> String
trId (Identifier s)  =  s

trVC :: VarClass -> String
trVC ObsV   =  _mathcal "O"
trVC ExprV  =  _mathcal "E"
trVC PredV  =  _mathcal "P"

trVCf :: VarClass -> String -> String
trVCf ObsV s = s
trVCf _ s = bold s

trVW :: VarWhen -> String
trVW Static      =  "."
trVW Before      =  ""
trVW (During m)  =  '_':m
trVW After       =  "'"
trVW Textual     =  "\""

trVar :: Variable -> String
trVar (Vbl i vc vw) = trVCf vc (trId i) ++ trVW vw

trLVar :: ListVar -> String
trLVar (LVbl (Vbl i vc vw) is js)
 = trVCf vc (trLId i) ++ trVW vw ++ trLess is js

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

trTerm :: Int -> Term -> String -- 1st arg is indent-level
trTerm i (Val tk k)           =  trValue k
trTerm i (Var tk v)           =  trVar v
trTerm i (Cons tk s [t1,t2])
 | isSymbId s                 = trInfix i t1 s t2
trTerm i (Cons tk n ts)       =  trId n ++ trApply i n ("( ",", "," )") ts
trTerm i (Bind tk n vs t)     =  trAbs i tk n (S.toList vs) t
trTerm i (Lam tk n vl t)      =  trAbs i tk n vl            t
trTerm i (Sub tk t sub)       =  trTerm i t ++ trSub i sub
trTerm i (Iter tk na ni lvs)
 =  trId na ++ "{"
            ++ trId ni ++ "("
                       ++ seplist "," trLVar lvs
                       ++ ")"
            ++ "}"
trTerm i (Type t)             =  trType t

trSub i (Substn tsub lvsub)
 = "[" ++
       trTL i "," rts ++ ',':trVL (map LstVar rlvs) ++
   "/" ++
       trVL (map StdVar tvs ++ map LstVar tlvs) ++
   "]"
 where
  (tvs,rts) = unzip $ S.toList tsub
  (tlvs,rlvs)  =  unzip $ S.toList lvsub
\end{code}

These will eventually do some sort of multi-line pretty-printing.
\begin{code}
trInfix i t1 s t2
 = "(" ++ trTerm i t1 ++ trId s ++ trTerm i t2 ++ ")"

trApply i n (lbr,sep,rbr) ts  =  lbr ++ trTL i sep ts ++ rbr

trTL i sep ts = seplist sep (trTerm i) ts

trAbs i tk n vl t
 = "("++trId n ++ ' ':trVL vl ++ spaced _bullet ++ trTerm i t ++ ")"

trVL = seplist "," trGVar
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
trLstVarMatchRole (KnownVarList vl)
  =  spaced _triangleq ++ _langle ++ trVL vl ++ _rangle
trLstVarMatchRole (KnownVarSet  vs)
  =  spaced _triangleq ++ "{" ++ trVL (S.toList vs) ++ "}"
trLstVarMatchRole UnknownListVar     =  " ?"
\end{code}

\begin{code}
trVarTable :: VarTable -> String
trVarTable vt
 = unlines [ trAssoc trVTVV $ vtList vt
           , trAssoc trVTLV $ stList vt
           , trAssoc trVTLV $ dtList vt
           ]

trVTVV (v,vmr)    =  trVar  v  ++ trVarMatchRole    vmr

trVTLV (lv,lvmr)  =  trLVar lv ++ trLstVarMatchRole lvmr
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
 = unlines [ trAssoc trVB vb, trAssoc trSB sb, trAssoc trLB lb ]

trAssoc tr pairs = "{ " ++ seplist ", " tr pairs ++ " }"

trVB ((i,vc),vb)
 = "(" ++ trId i ++ "." ++ trVC vc ++ ")" ++ spaced _maplet ++ trVarBind vb

trSB (s,t) = s ++ spaced _maplet ++ t

trLB ((i,vc,is,js),lvb)
  = "("  ++ trId i ++
    "$."  ++ trVC vc ++
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
