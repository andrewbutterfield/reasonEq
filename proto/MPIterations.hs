{- =============================================================================
 Want to match a collection of patterns against a collection of candidates
 in a MonadPlus setting

-}
module MPIterations where

import Data.Map(Map)
import qualified Data.Map as M
import Control.Monad

-- Reboot - we have  f :: MonadPlus mp => c -> p -> b -> mp b
-- where b' is (probably) b with extra stuff
type BasicF mp b c p = c -> p -> b -> mp b

type Combine c b b' = [c] -> [c] -> b -> b'

manyToOne :: MonadPlus mp
           => BasicF mp b c p
           -> Combine c b b'
           -> [c] -> p -> b
           -> mp b'
manyToOne bf cf [] p b = fail "."
manyToOne bf cf cs p b = manyToOne' bf cf [] p b cs

manyToOne' bf cf sc p b0 []      =  return $ cf sc [] b0
manyToOne' bf cf sc p b0 [c]     =  (do b <- bf c p b0 ; return $ cf sc [] b)
                                    -- `mplus`
                                    -- (return $ cf sc [c] b0)
manyToOne' bf cf sc p b0 (c:cs)  =  (do b <- bf c p b0 ; return $ cf sc cs b)
                                    `mplus`
                                    manyToOne' bf cf (c:sc) p b0 cs

-- returns all possible singelton matches
manyToMany :: MonadPlus mp
           => BasicF mp b c p
           -> Combine c b b'
           -> [c] -> [p] -> b
           -> mp b'
manyToMany bf cf cs [] b  =  return $ cf [] cs b
manyToMany bf cf cs ps b
 = foldr mplus (fail ".") $ map f ps
 -- = foldr mplus (return $ cf [] cs b) $ map f ps
 where
   f p = manyToOne bf cf cs p b

defCombine :: Combine c b (b,[c])
defCombine sc cs b  = (b, reverse sc ++ cs)

-- We need a manyToMany that that returns all possible mutliples.
-- This requires an ability to extract b, [c] from b'
type Extract c b b' = b' -> (b,[c])

manyToMultiple :: MonadPlus mp
               => BasicF mp b c p
               -> Combine c b b'
               -> Extract c b b'
               -> [c] -> [p] -> b
               -> mp b'
manyToMultiple bf cf xt cs [] b  =  return $ cf [] cs b
manyToMultiple bf cf xt cs (p:ps) b
 = do bc <- manyToOne bf cf cs p b
      let (b',cs') = xt bc
      manyToMultiple bf cf xt cs' ps b'


defExtract :: Extract c b (b,[c])
defExtract = id

-- concretise...

type Bind = Map Int Int

-- match if candidate arity same as pattern
mArity :: MonadPlus mp => BasicF mp Bind Int Int
mArity iC iP bind
 | even iC && even iP = return $ M.insert iP iC bind
 | odd iC && odd iP   = return $ M.insert iP iC bind
 | otherwise = fail "mArity differs"

manyToOneArity :: MonadPlus mp => [Int] -> Int -> Bind -> mp (Bind, [Int])
manyToOneArity = manyToOne mArity defCombine

manyToManyArity :: MonadPlus mp => [Int] -> [Int] -> Bind -> mp (Bind, [Int])
manyToManyArity = manyToMany mArity defCombine

manyToMultipleArity :: MonadPlus mp => [Int] -> [Int] -> Bind -> mp (Bind, [Int])
manyToMultipleArity = manyToMultiple mArity defCombine id
