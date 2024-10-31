\chapter{Universal Sets}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UnivSets (
  UnivSet(..)
, isListed
, dropset
, umbr, udiff, uunion, uintsct, unull, usubset, udisj, umap
) where
import Data.Set(Set)
import qualified Data.Set as S

-- import Debugger
\end{code}


\section{Introduction}

Here we extend (finite) sets to have an explicit universe indicator.

\begin{code}
data UnivSet a
  = Listed (Set a)
  | Everything -- (Set a) should be added so that `udiff` works properly
  deriving (Eq,Ord,Show,Read)


isListed :: UnivSet a -> Bool
isListed (Listed _)  =  True
isListed _           =  False

dropset :: Eq a => a -> (UnivSet a) -> Set a
dropset x Everything    =  S.singleton x
dropset _ (Listed vs)   =  vs 

usngl :: Ord a => a -> UnivSet a
usngl x = Listed $ S.singleton x

umbr :: Ord a => a -> UnivSet a -> Bool
umbr _ Everything  =  True
umbr x (Listed s)  =  x `S.member` s

udiff :: Ord a => (UnivSet a) -> (UnivSet a) -> (UnivSet a)
udiff _        Everything   =  Listed S.empty
udiff Everything  _         =  Everything -- approximation
udiff (Listed s) (Listed t)  =  Listed (s `S.difference` t)

uunion :: Ord a => (UnivSet a) -> (UnivSet a) -> (UnivSet a)
uunion _        Everything   =  Everything
uunion Everything  _         =  Everything
uunion (Listed s) (Listed t)  =  Listed (s `S.union` t)

uintsct :: Ord a => (UnivSet a) -> (UnivSet a) -> (UnivSet a)
uintsct uset1    Everything   =  uset1
uintsct Everything  uset2     =  uset2
uintsct (Listed s) (Listed t)  =  Listed (s `S.intersection` t)

unull :: Ord a => (UnivSet a) -> Bool
unull Everything = False
unull (Listed s)  = S.null s

usubset :: Ord a => (UnivSet a) -> (UnivSet a) -> Bool
usubset _        Everything   =  True
usubset Everything  _         =  False
usubset (Listed s) (Listed t)  =  s `S.isSubsetOf` t

udisj :: Ord a => (UnivSet a) -> (UnivSet a) -> Bool
udisj uset1    Everything   =  unull uset1
udisj Everything  uset2     =  unull uset2
udisj (Listed s) (Listed t)  =  S.null (s `S.intersection` t)

umap :: Ord a => (Set a -> Set a) -> (UnivSet a) -> (UnivSet a)
umap _ Everything   =  Everything
umap f (Listed s)  =  Listed $ f s
\end{code}

