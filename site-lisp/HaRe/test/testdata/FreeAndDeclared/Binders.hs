{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable  #-}
module FreeAndDeclared.Binders where

import Data.Generics

-- | Find the the new definition name in GHC.Name format.
findNewPName :: String -> RenamedSource -> Name
findNewPName name renamed = gfromJust "findNewPName" res
  where
     res = somethingStaged Renamer Nothing renamed
            -- (Nothing `mkQ` worker) renamed

     worker  (pname::Name)
        | (occNameString $ getOccName pname) == name = Just pname
     worker _ = Nothing

data Renamer = Renamer
somethingStaged = undefined
data Name = NameCon deriving Typeable
occNameString = undefined
getOccName = undefined
data RenamedSource = RNS
gfromJust = undefined
