module Scope1 where

-- import qualified Control.Parallel.Strategies as T

import qualified Control.Parallel.Strategies as S


-- should fail, as there are two possible qualifiers...

f x = let n1 = S.runEval (do n1' <- S.rpar n11
                             return n1')

      in n1 + n22
       where
        n11 = f (x+1)
        n22 = f (x+2)

