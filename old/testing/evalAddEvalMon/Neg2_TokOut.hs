module Neg2 where

import Control.Parallel.Strategies

f x = 42

b = f 76

g x = runEval $ do d <- f x; return d 