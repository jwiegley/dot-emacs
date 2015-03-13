module Case where

{- imports will be added for the PointlessP librasies -}

-- the hole expression will be selected for translation.
coswap = \x -> case x of Left y -> Right y
                         Right y -> Left y
