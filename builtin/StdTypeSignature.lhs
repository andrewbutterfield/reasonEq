\chapter{Standard Type Signature}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018--2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module StdTypeSignature (
  bool, boolf_1, boolf_2, boolf_3
, int, intf_1, intf_2, intf_3
, valueType
) where

import LexBase
import AST
\end{code}


\newpage
\section{Introduction}

Here we present a hard-coded implementation of basic types for \reasonEq.

\subsection{Booleans}

\begin{code}
bool = GivenType $ jId $ "B"
boolf_1 = FunType bool bool
boolf_2 = FunType bool boolf_1
boolf_3 = FunType bool boolf_2
\end{code}

\subsection{Integers}

\begin{code}
int = GivenType $ jId $ "Z"
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
