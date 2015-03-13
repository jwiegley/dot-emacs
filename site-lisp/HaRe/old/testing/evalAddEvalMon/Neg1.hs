module Neg1 where

import Control.Parallel.Strategies

f x = 42

b = f 76

g = runEval $ do d <- b; return d