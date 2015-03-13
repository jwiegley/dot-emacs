module MapDeclMPropStruct where

import MapDeclM
import HsPropStruct
import HsPropMaps

-- we assume only "expressions" & "declarations" may contain declarations
instance (MapDeclM pa ds,MapDeclM pp ds) => MapDeclM (PD i pa pp) ds where
    mapDeclM f = seqPD . mapPD return m m
      where m x = mapDeclM f x

instance (MapDeclM e ds,MapDeclM pa ds,MapDeclM pp ds)
       => MapDeclM (PA i e t pa pp) ds where
    mapDeclM f = seqPA . mapPA return m return m m
      where m x = mapDeclM f x

instance (MapDeclM e ds,MapDeclM pa ds,MapDeclM pp ds)
       => MapDeclM (PP i e p t pa pp) ds where
    mapDeclM f = seqPP . mapPP return m return return m m
      where m x = mapDeclM f x
