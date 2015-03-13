module LiftToTopLevel.Zmapq where

-- | Apply a generic query to the immediate children.
-- zmapQ :: GenericQ b -> Zipper a -> [b]
zmapQ f z = reverse $ downQ [] (g f)z

g f z'= query f z' : leftQ [] (g f)z'

downQ = undefined
query = undefined
leftQ = undefined
