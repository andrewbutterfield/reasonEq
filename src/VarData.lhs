\section{Variable Data}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module VarData ( VarMatchRole
               , pattern KnownConst, pattern KnownVar, pattern UnknownVar
               , VarTable
               , newVarTable
               , addKnownConst
               , addKnownVar
               , lookupVarTable, lookupVarTables
               ) where
--import Data.Maybe (fromJust)
import qualified Data.Map as M

--import Utilities
import LexBase
import AST
\end{code}

\subsection{Variable Matching Categories}

Variables,
whether of static, or any dynamic flavour,
can belong to one of three categories as regards matching:
\begin{description}
  \item[Known Constant]
    The variable is a shorthand for a known fixed value.
    It can only match itself, or that known value.
    Thr value can be basic like a number,
    or it could denote somethoing somewhat higher-order,
    such as a function or predicate.
  \item[Known Variable]
    The variable can take many possible values from a defined type,
    but it
    has a predefined interpretation.
    It can only match itself.
  \item[Unknown]
    Nothing specific is known about the variable.
    It can match anything of the appropriate flavour.
\end{description}
We refer, simply,
to variables in the first two categories above as ``known'',
while those in the third category are simply ``unknown''.
\begin{code}
data VarMatchRole -- Variable Matching Role
  =  KC Term  -- Known Constant
  |  KV Type  -- Known Variable
  |  UV       -- Unknown Variable
  deriving (Eq, Ord, Show, Read)

pattern KnownConst trm = KC trm
pattern KnownVar typ   = KV typ
pattern UnknownVar     = UV
\end{code}

\newpage
\subsection{Variable Tables}

We define simple lookup tables,
into which we can insert entries for known variables.
We use a newtype so we can control access.
\begin{code}
newtype VarTable
  = VT (M.Map Variable VarMatchRole)
  deriving (Show, Read)
\end{code}

\subsubsection{Creating New Table}

\begin{code}
newVarTable :: VarTable
newVarTable = VT M.empty
\end{code}

\subsubsection{Inserting into Table}

Adding values into a table overwrites any previous values
without any warning.
\begin{code}
addKnownConst :: Variable -> Term -> VarTable -> VarTable
addKnownConst var trm (VT table) =   VT $ M.insert var (KC trm) table

addKnownVar :: Variable -> Type -> VarTable -> VarTable
addKnownVar var typ (VT table) =   VT $ M.insert var (KV typ) table
\end{code}

\subsubsection{Table Lookup}

Lookup is total, returning \texttt{UV} if the variable is not present.
\begin{code}
lookupVarTable :: VarTable -> Variable -> VarMatchRole
lookupVarTable (VT table) var
 = case M.lookup var table of
     Nothing   ->  UV
     Just vmr  ->  vmr
\end{code}

We also have a version that searches a list of tables:
\begin{code}
lookupVarTables :: [VarTable] -> Variable -> VarMatchRole
lookupVarTables [] _ = UV
lookupVarTables (VT table:rest) var
 = case M.lookup var table of
     Just vmr  ->  vmr
     Nothing   ->  lookupVarTables rest var
\end{code}
