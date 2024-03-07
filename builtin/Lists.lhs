\chapter{Theory of Lists}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Lists (
  listAxioms, listName, listTheory
) where

import Data.Maybe
import qualified Data.Map as M

import LexBase
import Variables
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

\section{Lists Signature}


We need to build some infrastructure here.
This consists of the list variables $\sigma$, $\sigma_n$,
type constructor $\Seq{}$, and
the constants $\nil$, $\cons$, $\hd$, $\tl$, $\cat$, $\pfx$, 
 $\sngl$, $\rev$, $\elems$, $\len$.


\subsection{List Types}

These include:
\begin{code}
contt = TypeVar $ jId "t"
seqt  = star contt
seqf_1 t = FunType (star t) (star t)
seqf_2 t = FunType (star t) (seqf_1 t)
cons_t t = FunType t (seqf_1 t)
hd_t t   = FunType (star t) t
pfx_t t = FunType (star t) $ FunType (star t) bool
sngl_t t = FunType t (star t)
elems_t t = FunType (star t) (power t)
len_t t = FunType (star t) int
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
i_sngl  = jId "sngl"  ; snglIntro   = mkConsIntro i_sngl  $ sngl_t  contt
i_rev   = jId "rev"   ; revIntro    = mkConsIntro i_rev   $ seqf_1  contt
i_elems = jId "elems" ; elemslIntro = mkConsIntro i_elems $ elems_t contt
i_len   = jId "len"   ; lenlIntro   = mkConsIntro i_len   $ len_t   contt
\end{code}

\begin{code}
nilseq :: Term
nilseq = fromJust $ var seqt $ StaticVar i_nil
senum :: [Term] -> Term
senum ts = Cons seqt True i_seq ts
ssingle :: Term -> Term
ssingle t = senum [t]
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
    snglIntro $
    revIntro $
    elemslIntro $
    lenlIntro $
    newVarTable
\end{code}



\section{List Laws}

\begin{eqnarray*}
   \hd (x \cons \_) &\defs& x
\\ \tl (\_ \cons \sigma) &\defs& \sigma
\\ \nil \cat \sigma &\defs& \sigma
\\ (x \cons \sigma) \cat \sigma' &\defs& x \cons (\sigma \cat \sigma')
\\ \nil \pfx \sigma &\defs& \true
\\ (x \cons \sigma) \pfx (y \cons \sigma')
   &\defs&
   x = y \land \sigma \pfx \sigma'
\\ \sngl(x) &\defs& x \cons \nil
\\ \rev(\nil) &\defs& \nil
\\ \rev (x\cons \sigma) &\defs& \rev(\sigma) \cat \sngl(x)
\\ \elems(\nil) &\defs& \emptyset
\\ \elems (x\cons \sigma) &\defs& \setof{x} \cup \elems(\sigma)
\\ \len(\nil) &\defs& 0
\\ \len (\_\cons \sigma) &\defs& 1 + \len(\sigma) 
\end{eqnarray*}


Template
\begin{eqnarray*}
   x \mof \emptyset  &=& \false
\\ x \mof \seqof y   &=& x = y
\end{eqnarray*}
\vspace{-8pt}
\begin{code}
ax1 = ( "ax" -.- "1"
      , ( falseP
        , scTrue ) )
cj1 = ( "cj" -.-  "1"
      , ( trueP
        , scTrue ) )
\end{code}



We collect these together:
\begin{code}
listAxioms :: [Law]
listAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ ax1
      ]
\end{code}


Collecting \dots
\begin{code}
listConjectures :: [NmdAssertion]
listConjectures
  = map mkNmdAsn 
     [ cj1
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
