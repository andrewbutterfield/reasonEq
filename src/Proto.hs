module Proto
    ( someProto
    ) where

someProto :: IO ()
someProto
 = do let t = A (L "x" $ K (100/3)) (V "𝜔")
      --let tx = A (A (A n n) (A n n)) (A (A n n) (A n n))
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
