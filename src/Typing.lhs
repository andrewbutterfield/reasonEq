\chapter{Type Checking and Inference}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Typing where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import LexBase
import Variables
import AST
import FreeVars
import VarData
import Binding

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}

\newpage
\section{Introduction to Typing}

We implement the W algorithm for type inferencing, 
based on a version by Martin Grabm{\"u}ller
(https://github.com/mgrabmueller).
We follow the structure of that document.

\subsection{Preliminaries}

We have the following broad correspondance between his types and ours
(we use notation \texttt{<Typ:=val>} to denote 
a component of type \texttt{Typ} with a specifical value \texttt{val}):
\begin{verbatim}
data Lit          --> data Value = ...
  =  LInt Integer       |  Integer Integer
  |  LBool Bool         |  Boolean Bool
\end{verbatim}

\begin{verbatim}
data Type           --> data Type = ...  
  =  TVar String          |  TypeVar Identifier
  |  TInt                 |  GivenType <Identifer:="Z">
  |  TBool                |  GivenType <Identifer:="B">
  |  TFun Type Type       |  FunType Type Type
\end{verbatim}

\begin{verbatim}
data Exp                 --> data Term = ...
  =  EVar String               | Var TermKind Variable 
  |  ELit Lit                  | Val TermKind Value
  |  EApp Exp Exp              | Cons TermKind 
                                      Subable := ?
                                      Identifier := "apply"
                                      [Term] := [exp1,exp2]                
  |  EAbs String Exp           | Lam TermKind 
                                     Identifer := "lambda"
                                     VarList   := [Variable]
                                     Term
  |  ELet String Exp Exp       | Sub TermKind
                                     Term := exp2
                                     Substn :=  [exp1/var]
\end{verbatim}

We have to define our own versions of type-schemes and type-substitutions
\begin{code}
data TypeScheme = TS [String] Type
pattern Scheme qvars typ = TS qvars typ

type TypeSubst = Map Identifier Type
nullSubst :: TypeSubst
nullSubst = M.empty
\end{code}


We use the \h{Types} class from :
\begin{code}
class Types a where
    ftv    ::  a -> Set Identifier
    apply  ::  TypeSubst -> a -> a
\end{code}


