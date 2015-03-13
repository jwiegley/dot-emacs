module Abs where

{- imports will be added for the PointlessP librasies -}

import PointlessP.Combinators
import PointlessP.RecursionPatterns
import PointlessP.Isomorphisms
import PointlessP.Functors
-- the whole expression will be selected for translation: `\x -> x`
fun = app .
          (((curry (curry (curry ((snd . fst) . fst)))) .
                bang) /\
               id)
