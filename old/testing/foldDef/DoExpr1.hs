module DoExp1 where



f x = do
       (x:y) <- getLine
       putStrLn x


g x = do 
         x <- getLine
         putStrLn x

