\chapter{Standard Type Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module StdTypeSignature (
  boolf_1, boolf_2, boolf_3
, pred1
, apred1, apred11, apred2
, nat, int
, valueType
, powerSym, powerset, power
, starSym, listof, star
) where

import LexBase
import AST
\end{code}


\newpage
\section{Introduction}

Here we present a hard-coded implementation of basic types for \reasonEq.

\section{Predicates}

\subsection{Booleans}

\begin{code}
boolf_1 = FunType bool bool
boolf_2 = FunType bool boolf_1
boolf_3 = FunType bool boolf_2
\end{code}

\subsection{Predicate Function Types}

\begin{code}
pred1 = arbpred
i_t = jId "t"
tvar = TypeVar i_t
i_tn n = jId ("t"++show n)
tnvar n = TypeVar $ i_tn n
apred1 = FunType tvar bool
apred11 = FunType tvar apred1
apred2 = FunType (tnvar 1) $ FunType (tnvar 2) bool
\end{code}

\section{Expressions}


\subsection{Numbers}

\begin{code}
nat    = GivenType $ jId "N"
int    = GivenType $ jId "Z"
\end{code}


\subsubsection{\reasonEq\ Value Types}

\begin{code}
valueType :: Value -> Type
valueType (Integer _) = bool
valueType (Boolean _) = int
\end{code}

\subsection{Sets}

\begin{code}
powerSym  =  jId "P"
powerset  =  GivenType powerSym
power t   =  TypeCons powerSym [t]
\end{code}


\subsection{Lists}

\begin{code}
starSym  =  jId "*"
listof   =  GivenType starSym
star t   =  TypeCons starSym [t]
\end{code}

