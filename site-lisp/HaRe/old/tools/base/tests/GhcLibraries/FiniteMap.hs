-- Dummy FiniteMap module
module FiniteMap where

data FiniteMap key elt

emptyFM             :: FiniteMap key elt
unitFM              :: key -> elt -> FiniteMap key elt
lookupFM            :: Ord key => FiniteMap key elt -> key -> Maybe elt
listToFM            :: Ord key => [(key,elt)] -> FiniteMap key elt
fmToList            :: FiniteMap key elt -> [(key,elt)]
keysFM              :: FiniteMap key alt -> [key]
eltsFM              :: FiniteMap key alt -> [alt]
addListToFM         :: Ord key => FiniteMap key elt -> [(key,elt)] -> FiniteMap key elt
addListToFM_C :: Ord key => (elt -> elt -> elt) -> FiniteMap key elt -> [(key,elt)] -> FiniteMap key elt
lookupWithDefaultFM :: Ord key =>FiniteMap key elt -> elt -> key -> elt
mapFM               ::  (key -> elt1 -> elt2) -> FiniteMap key elt1 -> FiniteMap key elt2
isEmptyFM           :: FiniteMap key elt -> Bool
filterFM            :: Ord key => (key -> elt -> Bool)-> FiniteMap key elt -> FiniteMap key elt
delListFromFM       :: Ord key => FiniteMap key elt -> [key] -> FiniteMap key elt
plusFM              :: Ord key => FiniteMap key elt -> FiniteMap key elt -> FiniteMap key elt
elemFM              ::  Ord key => key -> FiniteMap key elt -> Bool
delFromFM           ::  Ord key => FiniteMap key elt -> key -> FiniteMap key elt
addToFM             ::  Ord key => FiniteMap key elt -> key -> elt -> FiniteMap key elt
sizeFM              ::   Ord key => FiniteMap key elt -> Int

emptyFM             = undefined
unitFM              = undefined
lookupFM            = undefined
listToFM            = undefined
fmToList            = undefined
keysFM              = undefined
eltsFM              = undefined
addListToFM         = undefined
addListToFM_C       = undefined
lookupWithDefaultFM = undefined
mapFM               = undefined
isEmptyFM           = undefined
filterFM            = undefined
delListFromFM       = undefined
plusFM              = undefined
elemFM              = undefined
delFromFM           = undefined
addToFM             = undefined
sizeFM              = undefined
