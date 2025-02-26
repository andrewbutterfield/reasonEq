\chapter{Theory of Arithmetic}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Arithmetic (
  i_neg, neg
, i_add, add
, i_sub, sub
, i_mul, mul
, i_div, div
, i_mod, imod
, zero, one
, arithmeticAxioms, arithmeticName, arithmeticTheory
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
import TestRendering
\end{code}

\section{Introduction}

We define a theory of integer arithmetic algebraically (laws only).

We support unary operator negation, 
and binary operators addition, subtraction, multiplication, 
and integer division and modulus.

\section{Arithmetic Signature}

\subsection{Arithmetic Types}

These are (curried) functions of one or two integers:
\begin{code}
intf_1 = FunType int int     -- Z -> Z
intf_2 = FunType int intf_1  -- Z -> Z -> Z
\end{code}

\subsection{Arithmetic Operators}

\begin{eqnarray*}
  -\_ &:& \Int \fun \Int
\\ +,-,*,\Div,\Mod &:& \Int \fun \Int \fun \Int
\end{eqnarray*}
\begin{code}
i_neg = jId "neg" ; negIntro = mkConsIntro i_neg intf_1
i_add = jId "+"   ; addIntro = mkConsIntro i_add intf_2
i_sub = jId "-"   ; subIntro = mkConsIntro i_sub intf_2
i_mul = jId "*"   ; mulIntro = mkConsIntro i_mul intf_2
i_div = jId "div" ; divIntro = mkConsIntro i_div intf_2
i_mod = jId "mod" ; modIntro = mkConsIntro i_mod intf_2
\end{code}

\begin{code}
neg :: Term -> Term
neg e = Cons int True i_neg [e]
add :: Term -> Term -> Term
add e f = Cons int True i_add [e,f]
sub :: Term -> Term -> Term
sub e f = Cons int True i_sub [e,f]
mul :: Term -> Term -> Term
mul e f = Cons int True i_mul [e,f]
idiv :: Term -> Term -> Term
idiv e f = Cons int True i_div [e,f]
imod :: Term -> Term -> Term
imod e f = Cons int True i_mod [e,f]
\end{code}


\subsection{Arithmetic Constants and Variables}

\begin{code}
zero = Val int (Integer 0)
one  = Val int (Integer 1)
ve = Vbl (jId "e") ExprV Static; e = fromJust $ eVar ArbType ve
vf = Vbl (jId "f") ExprV Static; f = fromJust $ eVar ArbType vf
vg = Vbl (jId "g") ExprV Static; g = fromJust $ eVar ArbType vg
\end{code}

\subsection{Arithmetic Known Variables}

\begin{code}
arithmeticKnown :: VarTable
arithmeticKnown 
  = negIntro $
    addIntro $
    subIntro $
    mulIntro $
    divIntro $
    modIntro $
    newNamedVarTable arithmeticName
\end{code}


\section{Arithmetic Laws}

We do addition and multiplication first,
then subtraction and negation,
and then finish with integer divisions, and mixed laws.

\subsection{Laws of Addition}

$$
\begin{array}{lll}
   \LWaddLUnit  && \LWaddLUnitN
\\ \LWaddRUnit  && \LWaddRUnitN
\\ e+f = f+e  && \QNAME{$+$-symm}
\\ e+(f+g) = (e+f)+g  && \QNAME{$+$-assoc}
\\ (e+f=e+g) \equiv (f=g)  && \QNAME{$+$-cancel}
\end{array}
$$\par\vspace{-4pt}
\begin{code}
axAddLUnit = ( "+" -.- "l" -.- "unit",
               (zero `add` e) `isEqualTo` e )
axAddRUnit = ( "+" -.- "r" -.- "unit",
               (e `add` zero) `isEqualTo` e )
axAddSymm = ( "+" -.- "symm",
               (e `add` f) `isEqualTo` (f `add` e) )
axAddAssoc = ( "+" -.- "assoc",
               (e `add` (f `add` g)) `isEqualTo` ((e `add` f) `add` g) )
axAddCancel = ( "+" -.- "cancel",
               ((e `add` f) `isEqualTo` (e `add` g)) 
               === 
               (f `isEqualTo` g) )
\end{code}

\subsection{Laws of Multiplication}

$$
\begin{array}{lll}
   1 * e = e  && \QNAME{$*$-l-unit}
\\ e * 1 = e  && \QNAME{$*$-r-unit}
\\ 0 * e = 0  && \QNAME{$*$-l-zero}
\\ e * 0 = 0  && \QNAME{$*$-r-zero}
\\ e * f = f * e  && \QNAME{$*$-symm}
\\ e * (f * g) = (e * f) * g  && \QNAME{$*$-assoc}
\\ (e * f=e * g) \equiv (f=g)  && \QNAME{$*$-cancel}
\end{array}
$$\par\vspace{-4pt}

\begin{code}
axMulLUnit = ( "*" -.- "l" -.- "unit",
               (one `mul` e) `isEqualTo` e )
axMulRUnit = ( "*" -.- "r" -.- "unit",
               (e `mul` one) `isEqualTo` e )
axMulLZero = ( "*" -.- "l" -.- "unit",
               (zero `mul` e) `isEqualTo` zero )
axMulRZero = ( "*" -.- "r" -.- "unit",
               (e `mul` zero) `isEqualTo` zero )
axMulSymm = ( "*" -.- "symm",
               (e `mul` f) `isEqualTo` (f `mul` e) )
axMulAssoc = ( "*" -.- "assoc",
               (e `mul` (f `mul` g)) `isEqualTo` ((e `mul` f) `mul` g) )
axMulCancel = ( "*" -.- "cancel",
               ((e `mul` f) `isEqualTo` (e `mul` g)) 
               === 
               (f `isEqualTo` g) )
\end{code}


\subsection{Laws of Subtraction}

$$
  \begin{array}{lll}
     e - 0 = e  && \QNAME{$-$-r-unit}
  \\ e - e = 0  && \QNAME{$-$-zero}
  \end{array}
$$\par\vspace{-4pt}
\begin{code}
axSubRUnit = ( "-" -.- "r" -.- "unit", (e `sub` zero) `isEqualTo` e )
axSubZero = ( "-" -.- "zero", (e `sub` e) `isEqualTo` zero )
\end{code}

\subsection{Laws of Negation}

$$
\begin{array}{lll}
   (-e) = (0-e)  && \QNAME{neg-def}
\\ (-0) = 0      && \QNAME{neg-zero}
\end{array}
$$\par\vspace{-4pt}
\begin{code}
axNegDef = ( "neg" -.- "def"
           , neg e `isEqualTo` (zero `sub` e) )
cjNegZero = ( "neg" -.- "zero"
            , neg zero `isEqualTo` zero )
\end{code}



\subsection{Laws of Integer Division}

$$
\begin{array}{lll}
   0 \Div e = 0  && \QNAME{$*$-l-zero}
\\ e \Div 1 = e  && \QNAME{$*$-r-unit}
\\ e \Div e = 1  && \QNAME{$*$-self}
\end{array}
$$\par\vspace{-4pt}
\begin{code}
axDivRUnit = ( "div" -.- "r" -.- "unit"
             , (e `idiv` one) `isEqualTo` e )
axDivLZero = ( "div" -.- "r" -.- "unit"
             , (zero `idiv` e) `isEqualTo` zero )
axDivSelf = ( "div" -.- "self"
            , (e `idiv` e) `isEqualTo` one)
\end{code}


\subsection{Laws of Integer Modulo}

$$
\begin{array}{lll}
     e \Mod e = 0  && \QNAME{mod-self}
\end{array}
$$\par\vspace{-8pt}
\begin{code}
axModSelf = ( "mod" -.- "self", (e `imod` e) `isEqualTo` zero ) 
\end{code}


\subsection{Laws of Mixed Arithmetic}

$$
\begin{array}{lll}
   e * (f + g) = e * f + e * g && \QNAME{$*$-$+$-distr}
\\ e + (-e) = 0  && \QNAME{$+$-inv}
\\ e - f = e + (-f) && \QNAME{$-$-alt-def}
\\ (-e) * f = -(e * f) && \QNAME{neg-$*$-distr}
\\ (e * f) \Div f = e && \QNAME{$*$-$\Div$-same}
\\ (-e) \Div f = -(e \Div f) && \QNAME{neg-$\Div$-distr}
\\ (e * f) \Mod f = 0 && \QNAME{$*$-$\Mod$-same}
\end{array}
$$\par\vspace{-4pt}
\begin{code}
axMulAddDistr = ( "*"-.-"+"-.-"distr" 
                , ( e `mul` (f `add` g) 
                    `isEqualTo` 
                    ((e `mul` f) `add` (e `mul` g)) )
                )
axAddInv = ( "+" -.- "inv"
           ,   (e `add` (neg e) `isEqualTo` zero ) )
axSubAltDef = ( "-" -.- "alt" -.- "def"
           ,   ((e `sub` f) `isEqualTo` (e `add` (neg f)) ) )
axNegMulDistr = ( "neg" -.- "*" -.- "distr"
                ,   ( (neg e) `mul` f )
                   `isEqualTo` 
                   neg (e `mul` f ) )
axMulDivSame = ( "*" -.- "div" -.- "same"
               ,   ( ((e `mul` f) `idiv` f)
                   `isEqualTo` 
                   e ) )
axNegDivDistr = ( "neg" -.- "div" -.- "distr"
                ,   ( (neg e) `idiv` f )
                   `isEqualTo` 
                   neg (e `idiv` f ) )
axMulModSame = ( "*" -.- "mod" -.- "same"
               ,   ( ((e `mul` f) `imod` f)
                   `isEqualTo` 
                   zero ) )
\end{code}


We collect these together:
\begin{code}
arithmeticAxioms :: [Law]
arithmeticAxioms
  = map (labelAsAxiom . mkNmdAsn . addSCtrue)
      [ axNegDef
      , axAddLUnit, axAddRUnit, axAddSymm, axAddAssoc, axAddCancel 
      , axSubRUnit, axSubZero
      , axMulLUnit, axMulRUnit, axMulLZero, axMulRZero
      , axMulSymm, axMulAssoc, axMulCancel, axNegMulDistr
      , axDivRUnit, axDivLZero, axDivSelf, axNegDivDistr
      , axMulAddDistr, axAddInv, axSubAltDef, axMulDivSame, axMulModSame
      ]

addSCtrue (nm,pred) = (nm, (pred,scTrue))
\end{code}

\section{Arithmetic Conjectures}

$$
\begin{array}{lll}
   e * (f - g) = e * f - e * g && \QNAME{$*$-$-$-distr}
\end{array}
$$\par\vspace{-4pt}
\begin{code}
cjMulSubDistr = ( "*" -.- "-" -.- "distr"
                , e `mul` (f `sub` g) 
                  `isEqualTo`
                  ((e `mul` f) `sub` (e `mul` g)) )
\end{code}


\begin{code}
arithmeticConjectures :: [NmdAssertion]
arithmeticConjectures
  = map (mkNmdAsn . addSCtrue) 
     [ cjMulSubDistr
     , cjNegZero
     ]
\end{code}

\section{The Arithmetic Theory}

\begin{code}
arithmeticName :: String
arithmeticName = "Arith"
arithmeticTheory :: Theory
arithmeticTheory
  =  nullTheory { thName  =  arithmeticName
                , thDeps  =  [ implName
                             , equivName 
                             , equalityName ]
                , known   =  arithmeticKnown
                , laws    =  arithmeticAxioms
                , conjs   =  arithmeticConjectures
                }
\end{code}
