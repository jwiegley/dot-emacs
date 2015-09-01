module InOut where

import PointlessP.Functors
import PointlessP.Combinators

{- imports will be added for the PointlessP librasies -}

-- the whole expression will be selected for translation.
tail' = \lst -> case (ouT (_L::[a]) lst) of
                    Left x -> inN (_L::[a]) (Left _L) 
                        -- if the list is emptu, return the empty list
                    Right x -> x
                        -- otherwise return the tail 
