module Case4 where
data T = C2 Int
 
caseIt x
    =   case x of
            42  ->  1 + (f   ((error
                                   "C1 no longer defined for T at line: 3")
                                  1
                                  2))
              where
                  f x =   error
                              "g (C1 1 2) no longer defined for T at line: 3"
 