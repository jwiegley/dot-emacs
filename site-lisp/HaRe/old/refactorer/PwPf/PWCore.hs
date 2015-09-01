-----------------------------------------------------------------------------
-- |
-- Module      :  PWCore
-- Copyright   :  (c) Jose Proenca 2005
-- License     :  GPL
--
-- Maintainer  :  jproenca@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- A syntax of a general pointwise language.
--
-----------------------------------------------------------------------------

module PWCore (
  {- | A simple definition of a pointwise language where:
        
        * products and sums are allowed;

        * constants are dealed by the use of /in/ and /out/ functions that
           allows to go from any type that has an associated base functor to and
           from a representation of that base functor using sums and products;

        * recursion is only possible by the use of the fixed point constructor.
  -}

  PWTerm (..)
) where

import RefacUtils

-- *Definition of the data type

data PWTerm = Unit               -- ^Unit
          | Var' String          -- ^Variable
          | PWTerm:@:PWTerm      -- ^Aplication
          | Abstr String PWTerm  -- ^Abstraction
          | PWTerm:><:PWTerm     -- ^Pair
          | Fst PWTerm           -- ^Point-wise first
          | Snd PWTerm           -- ^Point-wise second
          | Inl PWTerm           -- ^Point-wise left injection
          | Inr PWTerm           -- ^Point-wise right injection
          | Case PWTerm (String,PWTerm) (String,PWTerm)
                                 -- ^Case of
          | In  HsExpP PWTerm    -- ^Injection on a specified type
          | Out HsExpP PWTerm    -- ^Extraction of the functor of a specified type
          | Fix PWTerm
                                 -- ^Fixed point
            deriving Show
 
