\chapter{Theory of Arithmetic}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

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
z = GivenType $ jId $ "Z"
zf_1 = FunType z z     -- Z -> Z
zf_2 = FunType z zf_1  -- Z -> Z -> Z
\end{code}

\subsection{Arithmetic Operators}

\begin{eqnarray*}
  -\_ &:& \Int \fun \Int
\\ +,-,*,\Div,\Mod &:& \Int \fun \Int \fun \Int
\end{eqnarray*}
\begin{code}
i_neg = jId "neg" ; negIntro = mkConsIntro i_neg zf_1
i_add = jId "+"   ; addIntro = mkConsIntro i_add zf_2
i_sub = jId "-"   ; subIntro = mkConsIntro i_sub zf_2
i_mul = jId "*"   ; mulIntro = mkConsIntro i_mul zf_2
i_div = jId "div" ; divIntro = mkConsIntro i_div zf_2
i_mod = jId "mod" ; modIntro = mkConsIntro i_mod zf_2
\end{code}

\begin{code}
neg :: Term -> Term
neg e = ECons z True i_neg [e]
add :: Term -> Term -> Term
add e f = ECons z True i_add [e,f]
sub :: Term -> Term -> Term
sub e f = ECons z True i_sub [e,f]
mul :: Term -> Term -> Term
mul e f = ECons z True i_mul [e,f]
idiv :: Term -> Term -> Term
idiv e f = ECons z True i_div [e,f]
imod :: Term -> Term -> Term
imod e f = ECons z True i_mod [e,f]
\end{code}


\subsection{Arithmetic Constants and Variables}

\begin{code}
zero = Val (E z) (Integer 0)
one  = Val (E z) (Integer 1)
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
    newVarTable
\end{code}


\section{Arithmetic Laws}

We do addition and multiplication first,
then subtraxction ansd negation,
and then finish with integer divisions, and mixed laws.

\subsection{Laws of Addition}

\begin{verbatim}
add:
"plus-l-unit"  :  (zero `plus` e1) `equalZ` e1
"plus-r-unit"  :  (e1 `plus` zero) `equalZ` e1
"plus-comm"  :  (e1 `plus` e2) `equalZ` (e2 `plus` e1)
"plus-assoc"  :  (e1 `plus` (e2 `plus` e3)) `equalZ` ((e1 `plus` e2) `plus` e3)
"plus-cancel"  :  (e1 `equalZ` e2)===((e3 `plus` e1) `equalZ` (e3 `plus` e2))
\end{verbatim}

$$
  \begin{array}{lll}
     a = b  && \QNAME{whatever}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axWhat1 = ( "what" -.- "the"
            , ( e `isEqualTo` e
              , scTrue ) )
\end{code}

\subsection{Laws of Multiplication}

\begin{verbatim}
mul:
"mul-l-unit"  :  (one `mul` e1) `equalZ` e1
"mul-r-unit"  :  (e1 `mul` one) `equalZ` e1
"mul-l-zero"  :  (zero `mul` e1) `equalZ` zero
"mul-r-zero"  :  (e1 `mul` zero) `equalZ` zero
"mul-comm"  :  (e1 `mul` e2) `equalZ` (e2 `mul` e1)
"mul-assoc"  :  (e1 `mul` (e2 `mul` e3)) `equalZ` ((e1 `mul` e2) `mul` e3)
\end{verbatim}

$$
  \begin{array}{lll}
     a = b  && \QNAME{whatever}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axWhat3 = ( "what" -.- "the"
            , ( e `isEqualTo` e
              , scTrue ) )
\end{code}


\subsection{Laws of Subtraction}

\begin{verbatim}
sub:
"minus-l-unit"  :  (e1 `minus` zero) `equalZ` e1
\end{verbatim}

$$
  \begin{array}{lll}
     a = b  && \QNAME{whatever}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axWhat2 = ( "what" -.- "the"
            , ( e `isEqualTo` e
              , scTrue ) )
\end{code}

\subsection{Laws of Negation}

$$
  \begin{array}{lll}
     (-e) = (0-e)  && \QNAME{neg-def}
  \\ (-0) = 0      && \QNAME{neg-zero}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axNegDef = ( "neg" -.- "def"
            , ( neg e `isEqualTo` (zero `sub` e)
              , scTrue ) )
axNegZero = ( "neg" -.- "zero"
            , ( neg zero `isEqualTo` zero
              , scTrue ) )
\end{code}



\subsection{Laws of Integer Division}

\begin{verbatim}
div:
"divd-l-zero"  :  (zero `divd` e1) `equalZ` zero
"divd-r-unit"  :  (e1 `divd` one) `equalZ` e1
"divd-self"   :  (e1 `divd` e1) `equalZ` one
\end{verbatim}

$$
  \begin{array}{lll}
     a = b  && \QNAME{whatever}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axWhat4 = ( "what" -.- "the"
            , ( e `isEqualTo` e
              , scTrue ) )
\end{code}


\subsection{Laws of Integer Modulo}

$$
  \begin{array}{lll}
     e \Mod e = 0  && \QNAME{mod-self}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axWhat5 = ( "what" -.- "the"
            , ( e `isEqualTo` e
              , scTrue ) )
\end{code}


\subsection{Laws of Mixed Arithmetic}

\begin{verbatim}
mixed:
"plus-inv"  :  (e1 `plus` (neg e1)) `equalZ` zero
"minus-as-plus-neg"  :  (e1 `minus` e2) `equalZ` (e1 `plus` (neg e2))
"mul-div"  :  (e * f) `div`f = e
"mul-mod"  : (e * f) `mod` f = 0
\end{verbatim}

$$
  \begin{array}{lll}
     a = b  && \QNAME{whatever}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axWhat6 = ( "what" -.- "the"
            , ( e `isEqualTo` e
              , scTrue ) )
\end{code}



$$\begin{array}{ll}
   \AXequalRefl & \AXequalReflN
\end{array}$$

\vspace{-8pt}
\begin{code}
axEqualRefl
 = ( "=" -.- "refl"
   , ( e `isEqualTo` e
   , scTrue ) )
\end{code}

We collect these together:
\begin{code}
arithmeticAxioms :: [Law]
arithmeticAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [  ]
\end{code}

\section{Arithmetic Conjectures}


For now we don't have any conjectures.
\begin{code}
arithmeticConjectures :: [NmdAssertion]
arithmeticConjectures
  = map mkNmdAsn [  ]
\end{code}

\section{The Arithmetic Theory}

\begin{code}
arithmeticName :: String
arithmeticName = "Arithmetic"
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
