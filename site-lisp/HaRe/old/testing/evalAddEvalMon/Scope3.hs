module Scope3 where

import Control.Parallel.Strategies

f  = 42

b = f 76

g = runEval ( do d <- f; return d )


computation = f + b