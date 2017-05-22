module Proto
    ( someProto
    ) where

type Embed = Double

embed :: Int -> Double
embed = fromInteger . toInteger

minInt = -2^31 :: Int
maxInt = 2^31-1 :: Int

extract :: Double -> Int
extract = round

someProto :: IO ()
someProto
 = do let eyes = [minInt,minInt+1,minInt+10,-10,-1,0,1,10,maxInt-10,maxInt-1,maxInt] :: [Int]
      putStrLn ("eyes  = " ++ show eyes)
      let ds = map embed eyes
      putStrLn ("ds   = " ++ show ds)
      let is' = map extract ds
      putStrLn ("is'   = " ++ show is')

someProto'
 = do let n = A (L "x" $ K (100/3)) (V "𝜔")
      let t = A (A (A n n) (A n n)) (A (A n n) (A n n))
      putStrLn ("t  = " ++ show t)
      save t
      t' <- restore
      putStrLn ("t' = " ++ show t')
      putStrLn ("t==t' is " ++ show (t==t'))

data Test
 = K Double
 | V String
 | A Test Test
 | L String Test
 deriving (Eq,Ord,Show,Read)




lshow = unlines . lshow'

lshow' (K d) = ["(K "++show d++")"]
lshow' (V s) = ["(V "++show s++")"]
lshow' (A t1 t2)
 = ["(A "] ++ lshow' t1 ++ lshow' t2 ++ [")"]
lshow' (L v t)
 = ["(L "++ show v] ++ lshow' t ++ [")"]

save :: Test -> IO ()
save t = writeFile "test.sav" $ lshow t

restore :: IO Test
restore = fmap read $ readFile "test.sav"
