module DoExp2 where



f x = g undefined


g x = do 
         x <- getLine
         putStrLn x

