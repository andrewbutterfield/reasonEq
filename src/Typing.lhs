\chapter{Type Checking and Inference}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Typing where

import Data.Maybe
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
based on a version by Martin Grabm{\"u}ller (MG)
(https://github.com/mgrabmueller).
We follow the structure of that document.

\subsection{Preliminaries}

We have the following broad correspondance between MG types and ours
(we use notation \texttt{<Typ:=val>} to denote 
a component of type \texttt{Typ} with a specific value \texttt{val}).

The MG \h{Lit} type is a subset of our \h{Value} type:
\begin{verbatim}
data Lit          --> data Value = ...
  =  LInt Integer       |  Integer Integer
  |  LBool Bool         |  Boolean Bool
\end{verbatim}

The MG \h{Type} type is mainly a subset of our \h{Type},
where specific MG concrete types map to our \h{GivenType}
with meaningful identifiers.
\begin{verbatim}
data Type           --> data Type = ...  
  =  TVar String          |  TypeVar Identifier
  |  TInt                 |  GivenType <Identifer:="Z">
  |  TBool                |  GivenType <Identifer:="B">
  |  TFun Type Type       |  FunType Type Type
\end{verbatim}
\begin{code}
tInt   =  GivenType $ jId "Z"
tBool  =  GivenType $ jId "B"
\end{code}

The MG \h{Exp} type is very $\lambda$-calculus oriented,
whereas our \h{Term} type is very model-theoretic logic oriented.
We have a general $\lambda$ construct,
and can use \h{Cons} to represent the MG \h{EApp}.
However, there is no close correspondance for the MG \h{ELet}.
Here we exploit the law $\LET x = e_1 \IN e_2  =  e_2[e_1/x]$
and represent it using our \h{Sub} term.
\begin{verbatim}
data Exp                 --> data Term = ...
  =  EVar String               | Var TermKind Variable 
  |  ELit Lit                  | Val TermKind Value
  |  EApp Exp Exp              | Cons TermKind 
                                      Subable := ?
                                      Identifier := "@"
                                      [Term] := [exp1,exp2]                
  |  EAbs String Exp           | Lam TermKind 
                                     Identifer := "lambda"
                                     VarList   := [Variable]
                                     Term
  |  ELet String Exp Exp       | Sub TermKind
                                     Term := exp2
                                     Substn :=  [exp1/var]
\end{verbatim}
\begin{code}
eAbs :: Identifier -> Term -> Term
eAbs x t = fromJust $ lam arbtype lambda [StdVar $ StaticVar x] t
lambda = jId "lambda"
arbtype = E ArbType
eFApp :: Identifier -> Term -> Term
eFApp f t =  Cons arbtype False f [t]
eApp :: Term -> Term -> Term
eApp fun arg = Cons arbtype False aply [fun,arg]
aply = jId "@"
eLet :: Identifier -> Term -> Term -> Term
eLet x e1 e2 
  = Sub arbtype e2 $ jSubstn [(vx,e2)] []
  where vx = StaticVar x 
\end{code}

We have to define our own versions of type-schemes and type-substitutions
\begin{code}
data TypeScheme = TS [String] Type
pattern Scheme qvars typ = TS qvars typ

type TypeSubst = Map Identifier Type
nullSubst :: TypeSubst
nullSubst = M.empty
\end{code}


We use the MG \h{Types} class:
\begin{code}
class Types a where
    ftv    ::  a -> Set Identifier
    apply  ::  TypeSubst -> a -> a
\end{code}


