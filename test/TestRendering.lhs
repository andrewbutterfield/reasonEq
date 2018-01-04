\section{Test Rendering}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module TestRendering (
 trId, trVar
) where

import Data.Maybe(fromJust)
import Data.Map as M (fromList)
import qualified Data.Set as S
import Data.List (nub, sort, (\\), intersperse)


import Utilities
import LexBase
import Variables
import AST
import VarData
import Binding
import Matching
import MkTestBind
\end{code}

\newpage
\subsection{Test Rendering Intro.}

We provide a simple, almost certainly un-parsable,
rendering of datatypes to ease debugging.

\subsection{Variables}

\begin{code}
trId :: Identifier -> String
trId (Identifier s)  =  s

trVC :: VarClass -> String -> String
trVC _ s = s -- we don't show this explcitly now.

trVW :: VarWhen -> String
trVW Static      =  "."
trVW Before      =  ""
trVW (During m)  =  '_':m
trVW After       =  "'"
trVW Textual     =  "\""

trVar :: Variable -> String
trVar (Vbl i vc vw) = trVC vc (trId i) ++ trVW vw

trLVar :: ListVar -> String
trLVar (LVbl (Vbl i vc vw) is js)
 = trVC vc (trId i) ++ '$':trVW vw ++ trLess is js

trLess [] []  =  ""
trLess is js
  = '\\'
     : ( concat $ intersperse "," ( map trId is ++ map ((++ "$") . trId) js ) )
\end{code}

\newpage
\subsection{Types}

\begin{code}
trType :: Type -> String
trType ArbType            =  "*"
trType (TypeVar i)        =  trId i
trType (TypeApp i ts)     =  "(" ++ trId i ++ trTypes ts ++ ")"
trType (DataType i itss)  =  "ADT"
trType (FunType ta tr)    =  "("++ trType ta ++ " -> " ++ trType tr ++ ")"
trType (GivenType i)      =  "["++trId i++"]"

trTypes ts = concat $ intersperse " " $ map trType ts
\end{code}
