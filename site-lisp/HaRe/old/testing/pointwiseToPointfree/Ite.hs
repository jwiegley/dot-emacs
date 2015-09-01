module Ite where

{- imports will be added for the PointlessP librasies -}

-- the whole expression will be selected for translation.
notZero = \x -> if (== 0) x then False else True
