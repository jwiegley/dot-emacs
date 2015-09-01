module Monad2 where

data T1 = C1 Int Int | C2 Int Int


-- f :: Int -> m (T1 Int Int)
f x = do
        
        return (C1 x 2)


g = do
      (C1 x y) <- return (C1 1 2)
      putStrLn $ show x


