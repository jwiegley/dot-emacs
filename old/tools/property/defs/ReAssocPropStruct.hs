module ReAssocPropStruct where
import ReAssoc
import HsPropStruct
import HsPropMaps(mapPD,mapPA,mapPP)

instance (ReAssoc i pa,ReAssoc i pp) => ReAssoc i (PD i pa pp) where
  reAssoc env = mapPD id (reAssoc env) (reAssoc env)

instance (ReAssoc i e,ReAssoc i pa,ReAssoc i pp) => ReAssoc i (PA i e t pa pp)
   where reAssoc env = mapPA id (reAssoc env) id (reAssoc env) (reAssoc env)

instance (ReAssoc i e,ReAssoc i p,ReAssoc i pa,ReAssoc i pp)
       => ReAssoc i (PP i e p t pa pp)
   where
     reAssoc env = mapPP id r r id r r
       where r x = reAssoc env x
