{- =============================================================================
 Want to match a collection of patterns against a collection of candidates
 in a MonadPlus setting

-}
module MPIterations where

import Data.Map(Map)
import qualified Data.Map as M
import Control.Monad


type BMatch mp c p b = c -> p -> b -> mp b

type Bind = Map Int Int

-- match if candidate arity same as pattern
mArity :: MonadPlus mp => BMatch mp Int Int Bind
mArity iC iP bind
 | even iC && even iP = return $ M.insert iP iC bind
 | odd iC && odd iP   = return $ M.insert iP iC bind
 | otherwise = fail "mArity differs"

mwwe :: MonadPlus mp
     => (BMatch mp c p b) -> [c] -> p -> b
     -> mp (b,[c])
mwwe m cs p b = mwwe' m [] p b cs

mwwe' m sc p b [c]
 = do b' <- m c p b
      return (b',reverse sc)
mwwe' m sc p b (c:cs)
  = (do b' <- m c p b
        return (b',reverse sc++cs))
    `mplus`
    mwwe' m (c:sc) p b cs
