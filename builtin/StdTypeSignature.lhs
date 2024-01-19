\chapter{Standard Type Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module StdTypeSignature (
  bool, boolf_1, boolf_2, boolf_3
, nat, int, intf_1, intf_2, intf_3
, valueType
, pred1
, apred1, apred11, apred2
) where

import LexBase
import AST
\end{code}


\newpage
\section{Introduction}

Here we present a hard-coded implementation of basic types for \reasonEq.

\subsection{Booleans}

\begin{code}
bool    = GivenType $ jId $ "B"
boolf_1 = FunType bool bool
boolf_2 = FunType bool boolf_1
boolf_3 = FunType bool boolf_2
\end{code}

\subsection{Integers}

\begin{code}
nat    = GivenType $ jId "N"
int    = GivenType $ jId $ "Z"
intf_1 = FunType int int
intf_2 = FunType int intf_1
intf_3 = FunType int intf_2
\end{code}


\subsection{Value Types}

\begin{code}
valueType :: Value -> Type
valueType (Integer _) = bool
valueType (Boolean _) = int
\end{code}

\subsection{Predicate Function Types}

\begin{code}
pred1 = Pred 1
i_t = jId "t"
tvar = TypeVar i_t
i_tn n = jId ("t"++show n)
tnvar n = TypeVar $ i_tn n
apred1 = FunType tvar bool
apred11 = FunType tvar apred1
apred2 = FunType (tnvar 1) $ FunType (tnvar 2) bool
\end{code}
