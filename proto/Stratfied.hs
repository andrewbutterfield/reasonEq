{- =============================================================================
 We have a DAG implemented as Map n (Set n).
 Entering  n0 |-> { n1,n2,..,nk} into a DAG on succeeds
 if n1,..,nk are already present in its domain.

 Note this means that we can only enter n |-> {} into an empty DAG.

 Given n in DAG, we want to generate a list of n, such that domain
 elements occur before their range elements.
-}
module Stratified where

import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

{- -----------------------------------------------------------------------------

 Introduction

 We have an DAG, represented as a set-valued map
 with an insert as described above.

-}

type DAG a = Map a (Set a)

insDAG :: (Ord a, Monad m) => a -> (Set a) -> DAG a -> m (DAG a)
insDAG n ns dag
 | n `M.member` dag  =  fail "domain node already present"
 | ns `S.isSubsetOf` M.keysSet dag  =  return $ M.insert n ns dag
 | otherwise  =  fail "some range nodes not present"
