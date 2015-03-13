module LayoutIn4 where
main
    = io "hello"
  where
      io s
          =   do let k = reverse s
                 s <- getLine
                 let q = (k ++ s)
                 putStr q
                 putStr "foo"
 