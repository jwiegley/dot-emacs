module Triple1 where

-- import qualified Control.Parallel.Strategies as T

import qualified Control.Parallel.Strategies as S


-- should fail, as there are two possible qualifiers...

f x = let (n1, n22_2)
              =
                  S.runEval
                      (do n1' <- S.rpar n11
                          n22_2 <- S.rpar n22
                          return (n1', n22_2))

      in n1 + n22_2 + n33
       where
        n11 = f (x+1)
        n22 = f (x+2)
        n33 = f (x+3)

