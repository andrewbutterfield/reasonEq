\chapter{Theory of Lists}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Lists (
  nilseq, lenum, lsngl, hd, tl, cons, cat, pfx, rev, elems, len
, listAxioms, listName, listTheory
) where

import Data.Maybe
import qualified Data.Map as M

import LexBase
import Variables
import Types
import AST
import SideCond
import VarData
import Substitution
import Laws
import Proofs
import Theories
import StdTypeSignature
import StdSignature
import Equivalence
import Implication
import Equality
import ForAll
import TestRendering

import Arithmetic
import Sets
\end{code}

\section{Introduction}

Here we present a hard-coded implementation
a very simple theory of (typed) lists.

\newpage
\section{Lists Signature}


We need to build some infrastructure here.
This consists of the list variables $\sigma$, $\sigma_n$,
type constructor $\Seq{}$, and
the constants $\nil$, $\cons$, $\hd$, $\tl$, $\cat$, $\pfx$, 
 $\sngl$, $\rev$, $\elems$, $\len$.

We also want to have explicit list enumeration: $\seqof{a,b,\dots,z}$,
with the following mapping from this to the ``official'' nil/cons notation:
\begin{eqnarray*}
   \seqof{contents} &\defs& mklist(contents)
\\ mklist() &\defs& \nil
\\ mklist(a,rest) &\defs& a \cons mklist(rest)
\end{eqnarray*}


\subsection{List Types}

These include:
\begin{code}
contt     = TypeVar $ jId "t"    --   t
seqt      = star contt    --   t*
seqf_1 t  = FunType (star t) (star t)    --  t*->t*
seqf_2 t  = FunType (star t) (seqf_1 t)    --  t*->(t*->t*)
cons_t t  = FunType t        (seqf_1 t)    --  t->(t*->t*)
hd_t t    = FunType (star t) t    -- t*->t
pfx_t t   = FunType (star t) $ FunType (star t) bool    -- t*->(t*->B)
sngl_t t  = FunType t        (star t)    -- t->t*
elems_t t = FunType (star t) (power t)    -- t*->P t
len_t t   = FunType (star t) int    -- t*->N
\end{code}

\subsection{List Values/Operators}

\begin{eqnarray*}
   \nil &:& \Seq t
\\ \cons &:& t \fun \Seq t \fun \Seq t
\\ \hd &:& \Seq t \fun t
\\ \tl &:& \Seq t \fun \Seq t
\\ \cat &:& \Seq t \fun \Seq t \fun \Seq t
\\ \pfx &:& \Seq t \fun \Seq t \fun \Bool
\\ \sngl &:& t \fun \Seq t
\\ \rev &:& \Seq t \fun \Seq t
\\ \elems &:& \Seq t \fun \Set t
\\ \len &:& \Seq t \fun \Nat
\end{eqnarray*}
\begin{code}
i_nil   = jId "nil"   ; nilIntro    = mkConsIntro i_nil     seqt
i_cons  = jId "cons"  ; consIntro   = mkConsIntro i_cons  $ cons_t  contt
i_hd    = jId "hd"    ; hdIntro     = mkConsIntro i_hd    $ hd_t    contt
i_tl    = jId "tl"    ; tlIntro     = mkConsIntro i_tl    $ seqf_1  contt
i_seq   = jId "seq"   
i_cat   = jId "cat"   ; catIntro    = mkConsIntro i_cat   $ seqf_2  contt
i_pfx   = jId "pfx"   ; pfxIntro    = mkConsIntro i_pfx   $ pfx_t   contt
i_lsngl = jId "lsngl" ; snglIntro   = mkConsIntro i_lsngl $ sngl_t  contt
i_rev   = jId "rev"   ; revIntro    = mkConsIntro i_rev   $ seqf_1  contt
i_elems = jId "elems" ; elemslIntro = mkConsIntro i_elems $ elems_t contt
i_len   = jId "len"   ; lenlIntro   = mkConsIntro i_len   $ len_t   contt
\end{code}

\newpage
All list expressions are substitutable.
\begin{code}
r2T = reconcile2Types ; rTs = reconcileTypes
tOf = termtype ; j2T = join2Types ; jTs = joinTypes  -- shorthand

nilseq :: Term
nilseq      =  fromJust $ var seqt $ StaticVar i_nil
lenum :: [Term] -> Term
lenum ts    =  Cons (jTs ts) True i_seq ts
lsngl :: Term -> Term
lsngl t     =  lenum [t]
hd, tl, elems, len, rev :: Term -> Term
hd lst      =  Cons contt         True i_hd    [lst]
tl lst      =  Cons seqt          True i_tl    [lst]
elems lst   =  Cons (power contt) True i_elems [lst]
len lst     =  Cons int           True i_len   [lst]
rev lst     =  Cons (tOf lst)     True i_rev   [lst]
cons, cat, pfx :: Term -> Term -> Term
cons x lst  =  Cons (r2T (star $ tOf x) (tOf lst)) True i_cons [x,lst]
cat s1 s2   =  Cons (j2T s1 s2)                    True i_cat  [s1,s2]
pfx s1 s2   =  Cons (j2T s1 s2)                    True i_pfx  [s1,s2]
\end{code}


\subsection{List Constants and Variables}

\begin{code}
vS = StaticVar (jId "sigma") 
s = fromJust $ eVar seqt vS
vSn n = StaticVar (jId ("s"++show n)) 
sn n = fromJust $ eVar seqt $ vSn n
s1 = sn 1; s2 = sn 2; s3 = sn 3
vx = StaticVar (jId "x"); gvx = StdVar vx
x = fromJust $ eVar contt vx
vy = StaticVar (jId "y"); gvy = StdVar vy
y = fromJust $ eVar contt vy
\end{code}

\section{List Known Variables}

\begin{code}
listKnown :: VarTable
listKnown 
  = nilIntro $
    consIntro $
    hdIntro $
    tlIntro $
    catIntro $
    pfxIntro $
    -- snglIntro $   -- deprecated
    revIntro $
    elemslIntro $
    lenlIntro $
    newNamedVarTable listName
\end{code}


\newpage
\section{List Laws}

\subsubsection{List Constructors are Disjoint}

\begin{eqnarray*}
    \nil \neq (x \cons \ell)
    \equiv
    \false
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axListConsDisjoint 
  = ( "nil" -.- "cons" -.- "disj"
    , ( ( nilseq  `isEqualTo` (x `cons` s) )  ===  falseP
      , scTrue ) )
\end{code}

\subsubsection{List Constructor Equality}

\begin{eqnarray*}
    ((x_1 \cons \ell_1) = (x_2 \cons \ell_2))
    \equiv
    ( x_1 = x_2 \land \ell_1 = \ell_2)
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axConsEquality 
  = ( "cons" -.- "equality"
    , ( ( (x `cons` s1) `isEqualTo` (y `cons` s2))
        ===
        ( (x `isEqualTo` y) /\ (s1 `isEqualTo` s2) )    
      , scTrue ) )
\end{code}

\subsection{List Axioms}

\subsubsection{List Induction}

\begin{eqnarray*}
   P &\equiv&  P[\nil/\ell] \land ( P  \implies P[x \cons \ell/\ell] )
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
vLP = Vbl (jId "LP") PredV Static
gvLP = StdVar vLP
lP = jVar pred1 $ vLP
mksub p vts  = Sub pred1 p $ fromJust $ substn vts [] 
lst = Vbl (jId "lst") ExprV Static
axListInduction = ( "list" -.- "induction"
                  , ( lP 
                      ===
                      ( mksub lP [(vS,nilseq)]
                      /\
                      (lP ==> mksub lP [(vS,x `cons` s)]) )
                    , scTrue ) )
\end{code}

\subsection{Construction/Destruction}

\begin{eqnarray*}
   \hd (x \cons \_) &\defs& x
\\ \tl (\_ \cons \sigma) &\defs& \sigma
\\ \hd (x \cons \_) \cons \tl (\_ \cons \sigma)  &=& x \cons \sigma
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axHdDef = ( "hd" -.- "def"
          , ( hd (x `cons` s) `isEqualTo` x
            , scTrue ) )
axTlDef = ( "tl" -.- "def"
          , ( tl (x `cons` s) `isEqualTo` s
            , scTrue ) )
cjHdConsTl = ( "hd" -.-  "cons" -.- "tl"
             , ( (hd (x `cons` s)) `cons` (tl (x `cons` s)) 
                 `isEqualTo` 
                  (x `cons` s)
               , scTrue ) )
\end{code}


\subsection{Concatenation}

\begin{eqnarray*}
   \nil \cat \sigma &\defs& \sigma
\\ (x \cons \sigma) \cat \sigma' &\defs& x \cons (\sigma \cat \sigma')
\\ \sigma \cat \nil &=& \sigma
\\ \sigma_1 \cat (\sigma_2 \cat \sigma_2) 
    &=& (\sigma_1 \cat \sigma_2) \cat \sigma_2
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axNilCatDef = ( "nil" -.- "cat" -.- "def"
              , ( (nilseq `cat` s) `isEqualTo` s
                , scTrue ) )
axConsCatDef = ( "cons" -.- "cat" -.- "def"
               , ( ((x `cons` s1) `cat` s2) 
                   `isEqualTo` 
                   ( x `cons` (s1 `cat` s2))
                 , scTrue ) )
cjCatNil = ( "cat" -.-  "nil"
           , ( (s `cat` nilseq) `isEqualTo` s
           , scTrue ) )
cjCatAssoc =  ( "cat" -.-  "assoc"
              , ( (s1 `cat` (s2 `cat` s3))
                  `isEqualTo`
                  ((s1 `cat` s2) `cat` s3)
                , scTrue ) )
\end{code}

\newpage
\subsection{Prefix}

\begin{eqnarray*}
   \nil \pfx \sigma &\defs& \true
\\ (x \cons \sigma) \pfx (y \cons \sigma')
   &\defs&
   x = y \land \sigma \pfx \sigma'
\\ \sigma \pfx \nil &\defs& \sigma = \nil
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axNilPfx =  ( "nil" -.- "pfx" -.- "def"
            , ( nilseq `pfx` s
              , scTrue ) )
axConsPfx = ( "cons" -.- "pfx" -.- "def"
            , ( ((x `cons` s1) `pfx` (y `cons` s2))
                ===
                ((x `isEqualTo` y) /\ (s1 `pfx` s2))
              , scTrue ) )
axNilNilPfx =  ( "s" -.-  "pfx" -.- "nil"
               , ( (s `pfx` nilseq) === (s `isEqualTo` nilseq)
                 , scTrue ) )
\end{code}

\newpage
\subsection{Singleton}

This is deprecated for now,
as it requires some infrastructure to support explicit enumeration syntax.

\begin{eqnarray*}
   \sngl(x) &\defs& x \cons \nil
\\ \nil \pfx \sngl(x) &\equiv& \true
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axSnglDef = ( "lsngl" -.- "def"
            , ( (lsngl x) `isEqualTo` (x `cons` nilseq)
              , scTrue ) )
cjSnglPfx = ( "nil" -.-  "pfx" -.- "lsngl"
            , ( nilseq `pfx` (lsngl x)
              , scTrue ) )
\end{code}

\subsection{Reverse}

\begin{eqnarray*}
   \rev(\nil) &\defs& \nil
\\ \rev (x\cons \sigma) &\defs& \rev(\sigma) \cat \sngl(x)
\\ \rev(\rev(\sigma)) &=& \sigma
\\ \rev(\sigma_1 \cat \sigma_2) &=& \rev(\sigma_2) \cat \rev(\sigma_1)
\\ \rev(\sngl(x)) &=& \sngl(x)
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axRevNilDef = ( "rev" -.- "nil" -.- "def"
              , ( rev nilseq `isEqualTo` nilseq
                , scTrue ) )
axRevConsDef =  ( "rev" -.- "cons" -.- "def"
                , ( (rev (x `cons` s)) `isEqualTo` (rev s `cat` lsngl x)
                  , scTrue ) )
cjRevRevId =  ( "rev" -.-  "rev" -.- "id"
              , ( (rev (rev s)) `isEqualTo` s
                , scTrue ) )
cjRevCat =  ( "rev" -.-  "cat"
            , ( (rev (s1 `cat` s2)) `isEqualTo` ((rev s2) `cat` (rev s1))
              , scTrue ) )
cjRevSngl = ( "rev" -.-  "lsngl"
            , ( (rev (lsngl x)) `isEqualTo` lsngl x
              , scTrue ) )
\end{code}

\subsection{Elements}

\begin{eqnarray*}
   \elems(\nil) &\defs& \emptyset
\\ \elems (x\cons \sigma) &\defs& \setof{x} \cup \elems(\sigma)
\\ \elems(\sigma_1 \cat \sigma_2) &=& \elems(\sigma_1) \cup \elems(\sigma_2)
\\ \elems(\sngl(x)) &=& \setof{x}
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axElemsNilDef = ( "elems" -.- "nil" -.- "def"
                , ( (elems nilseq) `isEqualTo` mtset
                  , scTrue ) )
axElemsConsDef =  ( "elems" -.- "cons" -.- "def"
                  , ( (elems (x `cons` s))
                      `isEqualTo`
                      (ssingle x `sunion` elems s)
                    , scTrue ) )
cjElemsCat = ( "elems" -.-  "cat"
      , ( (elems (s1 `cat` s2)) `isEqualTo` (elems s1) `sunion` (elems s2)
        , scTrue ) )
cjElemsSngl = ( "elems" -.-  "lsngl"
      , ( (elems $ lsngl x) `isEqualTo` ssingle x
        , scTrue ) )
\end{code}

\subsection{Length}

\begin{eqnarray*}
   \len(\nil) &\defs& 0
\\ \len (\_\cons \sigma) &\defs& 1 + \len(\sigma) 
\\ \len(\sigma_1 \cat \sigma_2) &=& \len(\sigma_1) + \len(\sigma_2)
\\ \len(\sngl(x)) &=& 1
\\ \len(\rev(\sigma)) &=& \len(\sigma)
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
axLenNilDef = ( "len" -.- "nil" -.- "def"
              , ( (len nilseq) `isEqualTo` zero
                , scTrue ) )
axLenConsDef =  ( "len" -.- "cons" -.- "def"
                , ( (len (x `cons` s)) `isEqualTo` (one `add` len s)
                  , scTrue ) )
cjLenCat =  ( "len" -.-  "cat"
            , ( (len (s1 `cat` s2)) `isEqualTo` ((len s1) `add` (len s2))
              , scTrue ) )
cjLenSngl = ( "len" -.-  "lsngl"
            , ( (len $ lsngl x) `isEqualTo` one
              , scTrue ) )
cjLenRev =  ( "len" -.-  "rev"
            , ( (len $ rev s) `isEqualTo` len s
              , scTrue ) )
\end{code}


\section{Assembly}


We collect these together:
\begin{code}
listAxioms :: [Law]
listAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ axListConsDisjoint, axConsEquality, axListInduction
      , axHdDef, axTlDef
      , axNilCatDef, axConsCatDef
      , axNilPfx, axConsPfx, axNilNilPfx
      -- , axSnglDef    -- deprecated for now
      , axRevNilDef, axRevConsDef
      , axElemsNilDef, axElemsConsDef
      , axLenNilDef, axLenConsDef
      ]
\end{code}


Collecting \dots
\begin{code}
listConjectures :: [NmdAssertion]
listConjectures
  = map mkNmdAsn 
     [ cjHdConsTl
     , cjCatNil, cjCatAssoc
     -- , cjSnglPfx
     , cjRevRevId, cjRevCat
     -- , cjRevSngl   -- deprecated
     , cjElemsCat
     -- , cjElemsSngl   -- deprecated
     , cjLenCat, cjLenRev
     -- , cjLenSngl   -- deprecated
     ]
\end{code}

\section{The List Theory}

\begin{code}
listName :: String
listName = "Lists"
listTheory :: Theory
listTheory
  =  nullTheory { thName  =  listName
                , thDeps  =  [ implName
                             , equivName 
                             , equalityName
                             , forallName
                             , arithmeticName
                             , setName
                             ]
                , known   =  listKnown
                , laws    =  listAxioms
                , conjs   =  listConjectures
                }
\end{code}
