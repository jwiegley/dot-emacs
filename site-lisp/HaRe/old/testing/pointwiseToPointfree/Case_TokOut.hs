module Case where

{- imports will be added for the PointlessP librasies -}

import PointlessP.Combinators
import PointlessP.RecursionPatterns
import PointlessP.Isomorphisms
import PointlessP.Functors
-- the hole expression will be selected for translation.
coswap = app .
             (((curry
                    (app .
                         ((curry (((Right . snd) \/ (Left . snd)) . distr)) /\
                              snd))) .
                   bang) /\
                  id)
