module DoExp2 where



f x = do
       t <- getLine
       putStrLn t


g x = do 
         x <- getLine
         putStrLn x

