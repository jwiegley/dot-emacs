module Monad1 where


{- f3 :: Num t  => String  ->  (IO String, IO t) -}
f3 x
    =   (do putStrLn x
            return x,
         do putStrLn "hello"
            return 42)
f :: [Char] -> IO String
f x = do
        putStrLn x
        return x

f2 :: [Char] -> IO Int
f2 x = do 
           putStrLn "hello"
           return 42