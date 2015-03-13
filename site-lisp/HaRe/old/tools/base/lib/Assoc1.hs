module Assoc1 where

import Products (fork)
import Maybe (listToMaybe, fromJust)

-- import FiniteMap


-- useful to sometimes specify types
type IdAt a = a -> a 


class Eq k => IsAssoc a k where
    ascEmpty        :: a k v
    ascFromList     :: [(k,v)] -> a k v
    ascToList       :: a k v -> [(k,v)]
    ascAddList      :: a k v -> [(k,v)] -> a k v

    ascLookup       :: a k v -> k -> Maybe v
    ascLookupAll    :: a k v -> k -> [v]
    ascKeys         :: a k v -> [k]
    ascVals         :: a k v -> [v]
    ascMap          :: (k -> v -> w) -> a k v -> a k w

    ascLookupAll a x= [ v | (k,v) <- ascToList a, k == x ]
    ascLookup a     = listToMaybe . ascLookupAll a  
    ascEmpty        = ascFromList []


ascLOOKUP :: IsAssoc a k => a k v -> k -> v
ascLOOKUP a = fromJust . ascLookup a


newtype AscList k v = AL { unAL :: [(k,v)] }

instance Eq k => IsAssoc AscList k where
    ascEmpty                = AL []
    ascAddList (AL a) y     = AL (a ++ y)
    ascLookup (AL a) x      = lookup x a
    ascKeys                 = map fst . unAL
    ascVals                 = map snd . unAL
    ascFromList             = AL
    ascToList               = unAL
    ascMap f                = AL . map (fork fst (uncurry f)) . unAL
    
  {-  
instance Ord k => IsAssoc FiniteMap k where
    ascEmpty    = emptyFM
    ascFromList = listToFM
    ascToList   = fmToList
    ascAddList  = addListToFM
    ascLookup   = lookupFM
    ascKeys     = keysFM
    ascVals     = eltsFM
    ascMap      = mapFM
     
-}

    
