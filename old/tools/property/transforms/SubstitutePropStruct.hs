module SubstitutePropStruct where
import Substitute
import HsPropStruct
import HsPropMaps
import PropSyntaxStruct(mapProp,Prop)

instance (MapExp e pa,MapExp e pp) => MapExp e (PD i pa pp) where
  mapExp f = mapPD id (mapExp f) (mapExp f)

instance (MapExp e pa,MapExp e pp) => MapExp e (PA i e t pa pp) where
  mapExp f = mapPA id f id (mapExp f) (mapExp f)

instance (MapExp e pa,MapExp e pp) => MapExp e (PP i e p t pa pp) where
  mapExp f = mapPP id f id id (mapExp f) (mapExp f)

instance (MapExp e b,MapExp e p) => MapExp e (Prop b p) where
  mapExp f = mapProp (mapExp f) (mapExp f)
