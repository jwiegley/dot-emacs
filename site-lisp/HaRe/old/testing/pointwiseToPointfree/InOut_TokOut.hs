module InOut where

import PointlessP.Functors
import PointlessP.Combinators
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
{- imports will be added for the PointlessP librasies -}

-- the whole expression will be selected for translation.
tail' = app .
            (((curry
                   (app .
                        ((curry
                              ((((inN (_L :: [a])) . (Left . bang)) \/ snd) .
                                   distr)) /\
                             ((ouT (_L :: [a])) . snd)))) .
                  bang) /\
                 id)
                        -- otherwise return the tail 
