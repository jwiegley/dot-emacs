module LiftToTopLevel.Zmapq where

-- | Apply a generic query to the immediate children.
-- zmapQ :: GenericQ b -> Zipper a -> [b]
zmapQ f z = reverse $ downQ [] g z where
  g z' = query f z' : leftQ [] g z'


downQ = undefined
query = undefined
leftQ = undefined
