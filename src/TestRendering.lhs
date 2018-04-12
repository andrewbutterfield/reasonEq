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
 , trValue, trTerm, trSideCond
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

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Binding
import Matching
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


Based on some prototyping (\texttt{inproto/TRYOUT.hs},  April 2018),
we re-factor a show-function $S$ for terms of the form
$S(K~t_1~\dots~t_n) \defs asmK(\dots S(t1)\dots S(tn)\dots)$
into
\begin{eqnarray*}
   S(K~t_1~\dots~t_n) &\defs& AK(t_1,\dots,t_n)
\\ AK(t_1,\dots,t_n)   &\defs& asmK(\dots S(t1)\dots S(tn)\dots)
\end{eqnarray*}
This makes it very easy to then render term zippers,
with a facility to highlight the focus.
With precedence values, the picture is a little more complicated:
\begin{eqnarray*}
   S_p(K~t_1~\dots~t_n) &\defs& AK_p(t_1,\dots,t_n)
\\ AK_p(t_1,\dots,t_n)   &\defs& asmK_p(\dots S_{p_1}(t_1)\dots S_{p_n}(t_n)\dots)
\end{eqnarray*}
Here the recursive $p_i$ for $t_i$ depends on $i$,
and not the precedence of the top level operator, if any,
in $t_i$.
This dependency needs to be explcitly recorded in order for
zipper rendering to handle precedence rules properly.
\begin{eqnarray*}
   S_p(K~t_1~\dots~t_n) &\defs& AK_p(t_1,\dots,t_n)
\\ AK_p(t_1,\dots,t_n)  &\defs&
                    asmK_p(\dots S_{pdepK(1)}(t_1)\dots S_{pdefK(n)}(t_n)\dots)
\\ pdepK(i) &\defs& \textsf{rendering context of $i$th term of $K$}
\end{eqnarray*}
The simplest case is when $K$ is a binary operator of precedence $p_K$,
in which case $pdepK(i) = p_K$, for all $i$.

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

\begin{code}
type InfixKind = ( Int     -- precedence
                 , Bool )  -- true if *syntactically* associative
prc :: Identifier -> InfixKind
prc (Identifier n)
  | n == "="       =  (1,False)
  | n == _equiv    =  (2,False)
  | n == _implies  =  (3,False)
  | n == _lor      =  (4,True)
  | n == _land     =  (5,True)
  | n == _lnot     =  (6,False)
  | otherwise      =  (0,False) -- force parenthesising if not at top-level
\end{code}

\newpage
\begin{code}
trTerm :: Int -> Term -> String -- 1st arg is precedence (not yet used)
trTerm p (Val tk k)           =  trValue k
trTerm p (Var tk v)           =  trVar v

trTerm p (Cons tk s ts@(_:_:_))
 | isSymbId s                 =  trInfix p s ts
trTerm p (Cons tk n [t])
 | isAtomic t                 =  trId n ++ trTerm 0 t
trTerm p (Cons tk n ts)       =  trId n ++ trApply p n ("(",", ",")") ts

trTerm p (Bind tk n vs t)     =  trAbs p tk n (S.toList vs) t
trTerm p (Lam tk n vl t)      =  trAbs p tk n vl            t
trTerm p (Sub tk t sub)       =  trTerm p t ++ trSub p sub

trTerm p (Iter tk na ni lvs)
 =  trId na ++ "{"
            ++ trId ni ++ "("
                       ++ seplist "," trLVar lvs
                       ++ ")"
            ++ "}"
trTerm p (Type t)             =  trType t
\end{code}

\begin{code}
trSub p (Substn tsub lvsub)
 = "[" ++
       trTL p "," rts ++ ',':trVL (map LstVar rlvs) ++
   "/" ++
       trVL (map StdVar tvs ++ map LstVar tlvs) ++
   "]"
 where
  (tvs,rts) = unzip $ S.toList tsub
  (tlvs,rlvs)  =  unzip $ S.toList lvsub
\end{code}

These will eventually do some sort of multi-line pretty-printing.
\begin{code}
trInfix p s ts
 = let (ps,isAssoc) = prc s in
     trBracketIf (ps < p || ps == p && not isAssoc)
                 $ intercalate (trId s) $ map (trTerm ps) ts

trBracketIf True  s  =  "("++s++")"
trBracketIf False s  =  s

trApply p n (lbr,sep,rbr) ts  =  lbr ++ trTL p sep ts ++ rbr

trTL p sep ts = seplist sep (trTerm p) ts

trAbs p tk n vl t
 = "("++trId n ++ ' ':trVL vl ++ spaced _bullet ++ trTerm p t ++ ")"

trVL = seplist "," trGVar

trVList vl  =  _langle ++ trVL vl ++ _rangle
trVSet vs   =  "{" ++ trVL (S.toList vs) ++ "}"
\end{code}

\subsection{Side Conditions}

\begin{code}
trSideCond (SC vs vscmap)
 = intcalNN ";" (trFresh vs : trVarSCMap vscmap)

trFresh vs
 | S.null vs  =  ""
 | otherwise = "fresh"++ trVSet vs

trVarSCMap vscmap = map trVarSideCond $ M.assocs vscmap
trVarSideCond (v,(Exact vs)) = trVSet vs ++ "=" ++ trVar v
trVarSideCond (v,(Approx pre mD mC))
 = intcalNN ";" [trPre pre,trD mD,trC mC]
 where
   trPre True = "pre("++trVar v++")" ; trPre False = ""
   trD Nothing = ""
   trD (Just vs) = trVSet vs ++ _lnot ++ _in ++ trVar v
   trC Nothing = ""
   trC (Just vs) = trVar v ++ _subseteq ++ trVSet vs
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
 = unlines' [ trAssoc trVTVV $ vtList vt
            , trAssoc trVTLV $ stList vt
            , trAssoc trVTLV $ dtList vt
            ]

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
 = unlines' [ trAssoc trVB vb, trAssoc trSB sb, trAssoc trLB lb ]

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
