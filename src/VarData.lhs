\section{Variable Data}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module VarData ( VarMatchRole
               , pattern KnownConst, pattern KnownVar, pattern UnknownVar
               , isKnownConst, isKnownVar, isUnknownVar
               , vmrConst, vmrType
               , LstVarMatchRole
               , pattern KnownVarList, pattern AnyVarList
               , VarTable
               , vtList, ltList
               , newVarTable
               , addKnownConst
               , addKnownVar
               , addKnownListVar
               , lookupVarTable, lookupVarTables
               , lookupLVarTable, lookupLVarTables
               , isAcyclicVarTable
               ) where
--import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (nub)

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
    The variable is static,
    and is a shorthand for a known fixed value.
    It can only match itself, or that known value.
    The value can be basic like a number,
    or it could denote something somewhat higher-order,
    such as a function or predicate.
  \item[Known Variable]
    The variable is an observation
    and can take many possible values from a defined type.
    it has a predefined interpretation,
    and can only match itself.
  \item[Unknown]
    Nothing specific is known about the variable.
    It can match anything of the appropriate ``flavour''.
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

isKnownConst, isKnownVar, isUnknownVar :: VarMatchRole -> Bool
isKnownConst (KC _) = True
isKnownConst _ = False
isKnownVar (KV _) = True
isKnownVar _= False
isUnknownVar UV = True
isUnknownVar _ = False

vmrConst :: VarMatchRole -> Term
vmrConst (KC trm)  =  trm
vmrConst (KV _)    =  error "vmrCont: var. match role is KnownVar"
vmrConst UV        =  error "vmrCont: var. match role is UnknownVar"

vmrType :: VarMatchRole -> Type
vmrType (KV typ)  =  typ
vmrType (KC _)    =  error "vmrType: var. match role is KnownConst"
vmrType UV        =  error "vmrType: var. match role is UnknownVar"
\end{code}

\subsection{List-Variable Matching Categories}

List-variables can match either any list of variables,
or can also be ``known'',
as a name for a specific list of variables.
\begin{code}
data LstVarMatchRole -- ListVar Matching Roles
 = KL VarList -- Known Variable-List
 | AL         -- Arbitrary Variable-List
 deriving (Eq, Ord, Show, Read)

pattern KnownVarList vl = KL vl
pattern AnyVarList      = AL
\end{code}

\newpage
\subsection{Variable Tables}

We define simple lookup tables,
into which we can insert entries for known variables and list-variables.
We use a newtype so we can control access.
\begin{code}
newtype VarTable
  = VT ( Map Variable VarMatchRole
       , Map ListVar  LstVarMatchRole )
  deriving (Eq, Show, Read)
\end{code}

We will want to inspect tables.
\begin{code}
vtList :: VarTable -> [(Variable,VarMatchRole)]
vtList (VT (vtable, _)) = M.toList vtable
ltList :: VarTable -> [(ListVar,LstVarMatchRole)]
ltList (VT (_, ltable)) = M.toList ltable
\end{code}


\subsubsection{Creating New Table}

\begin{code}
newVarTable :: VarTable
newVarTable = VT (M.empty, M.empty)
\end{code}

\subsubsection{Inserting into Table}

Adding values into a table overwrites any previous values
without any warning.

Only static variables may name a constant:
\begin{code}
addKnownConst :: Monad m => Variable -> Term -> VarTable -> m VarTable
addKnownConst var@(Vbl _ _ Static) trm (VT (vtable,ltable))
  =  return $ VT ( M.insert var (KC trm) vtable, ltable )
addKnownConst _ _ _ = fail "addKnownConst: not for Dynamic Variables."
\end{code}

Only observation variables can
range over values of a given type.
\begin{code}
addKnownVar :: Monad m => Variable -> Type -> VarTable -> m VarTable
addKnownVar var@(ObsVar _ _) typ (VT (vtable, ltable))
  = return $ VT ( M.insert var (KV typ) vtable, ltable )
addKnownVar _ _ _ = fail "addKnownVar: not for Expr/Pred Variables."
\end{code}

For now only observation-list variables
can be defined as equal to a list of general variables,
with the same temporality
(except if static, these can mix and match temporal aspects).
\begin{code}
addKnownListVar :: Monad m => ListVar -> VarList -> VarTable -> m VarTable
addKnownListVar lv vl (VT (vtable, ltable))
 | [whatLVar lv] == nub (map whatGVar vl)
                             =  return $ VT (vtable, M.insert lv (KL vl) ltable)
 | otherwise = fail  "addKnownListVar: inconsistent variable classifications."
\end{code}

\subsubsection{Table Lookup}

Variable lookup is total, returning \texttt{UV} if the variable is not present.
\begin{code}
lookupVarTable :: VarTable -> Variable -> VarMatchRole
lookupVarTable (VT (vtable, _)) var
 = case M.lookup var vtable of
     Nothing   ->  UV
     Just vmr  ->  vmr
\end{code}

We also have a version that searches a list of tables:
\begin{code}
lookupVarTables :: [VarTable] -> Variable -> VarMatchRole
lookupVarTables [] _ = UV
lookupVarTables (VT (vtable,_):rest) var
 = case M.lookup var vtable of
     Just vmr  ->  vmr
     Nothing   ->  lookupVarTables rest var
\end{code}

Repeating for list-variables:
\begin{code}
lookupLVarTable :: VarTable -> ListVar -> LstVarMatchRole
lookupLVarTable (VT (_,ltable)) lvar
 = case M.lookup lvar ltable of
     Nothing    ->  AL
     Just lvmr  ->  lvmr

lookupLVarTables :: [VarTable] -> ListVar -> LstVarMatchRole
lookupLVarTables [] _ = AL
lookupLVarTables (VT (_,ltable):rest) lvar
 = case M.lookup lvar ltable of
     Just lvmr  ->  lvmr
     Nothing    ->  lookupLVarTables rest lvar
\end{code}

\newpage
\subsection{Ensuring \texttt{VarTable} Acyclicity}

We need to ensure that there are no cycles in any \texttt{VarTable}.
We do this by a recursive walk over the mappings,
building a mapping from each variable type to a set of the same type.
\begin{code}
type ItemDep v = Map v (Set v)
\end{code}
Given a mapping and a specialised list-valued lookup,
we build an item dependency map,
checking for self-inclusion all the way.
\begin{code}
isAcyclic :: Ord d
          => Map d r -- the map, where 'r' contains one or more 'd's.
          -> (Map d r -> d -> Set d) -- specialised lookup
          -> Bool  -- true if map is acyclic in 'd'
isAcyclic m lkp = isAcyclic' m lkp M.empty (M.keys m)
\end{code}
We work through the keys accumulating the item-dependency map.
\begin{code}
isAcyclic' :: Ord d
           => Map d r -- the map, where 'r' contains one or more 'd's.
           -> (Map d r -> d -> Set d) -- specialised lookup
           -> ItemDep d -- accumulating map
           -> [d]  -- keys remaining to be processed
           -> Bool
isAcyclic' _ _ dds [] = isAcyclic'' dds
isAcyclic' m lkp dds (d:ds)
  = isAcyclic' m lkp (M.insertWith (S.union) d (lkp m d) dds) ds
\end{code}
We test the dependency map for cycles,
which first involves computing the transitive closure.
\begin{code}
isAcyclic'' dds = False
\end{code}

Everytime the mapping is extended we check for self-inclusion.
\begin{code}
isAcyclicVarTable :: VarTable -> Bool
isAcyclicVarTable (VT (vtable, ltable))
 = isAcyclic vtable vlkp
   &&
   isAcyclic ltable llkp
 where

   vlkp vtbl v
     = case M.lookup v vtbl of
         Just (KnownConst (Var _ v@(Vbl _ _ _)))  ->  S.singleton v
         _                                        ->  S.empty

   llkp ltbl lv
     = case M.lookup lv ltbl of
        Just (KnownVarList vl)  ->  S.fromList $ listVarsOf vl
        _                       ->  S.empty

\end{code}
