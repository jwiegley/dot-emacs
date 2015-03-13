module NameMapsPropDecorate where
import NameMaps
import TiPropDecorate
--import PropSyntax(AssertionI,PredicateI)
import NameMapsDecorate(mts)
import TiTypes
--import TiKinds
import NameMapsProp()
--import NameMapsPropStruct(bothtype,bothval)
import HsIdent(mapHsIdent2)
import MapDeclM
--import MapDeclMBaseStruct()
import MapDeclMPropStruct()
import MUtils
import AccList

instance AccNames i (TiDecls i) where
  accNames f (Decs ds (ks,ts)) = accNames f ds . accNames f ts -- hmm, ks?

instance AccNames i (TiDecl i) where
  accNames f (Dec d) = accNames f d

instance AccNames i (TiExp i) where
  accNames f (Exp e) = accNames f e
  accNames f (TiSpec i _ ts) = accNames f i . accNames f ts
  accNames f (TiTyped e t) = a e . a t
    where a x = accNames f x

instance AccNames i (TiAssertion i) where accNames = accNamesRec
instance AccNames i (TiPredicate i) where accNames = accNamesRec

instance AccNames i (OTiAssertion i) where
  accNames f (OA is ds pa) = accList f is . accNames f ds . accNames f pa

--------------------------------------------------------------------------------

instance MapNames i1 (TiDecls i1) i2 (TiDecls i2) where
  mapNames2 c f (Decs ds (ks,ts)) = Decs (m ds) (mks ks,mts c f ts)
    where
      m x = mapNames2 c f x
      mks = map mk
      mk (i:>:(k,ti)) = bothtype mapHsIdent2 f i:>:(k,m ti)

instance MapNames i1 (TiDecl i1) i2 (TiDecl i2) where
  mapNames2 c f (Dec d) = Dec (mapNames2 c f d)

instance MapNames i1 (TiExp i1) i2 (TiExp i2) where
  mapNames2 c f (Exp e) = Exp (mapNames2 c f e)
  mapNames2 c f (TiSpec i sc ts)= TiSpec (bothval mapHsIdent2 f i) (m sc) (m ts)
    where m x = mapNames2 c f x
  mapNames2 c f (TiTyped e t) = TiTyped (m e) (m t)
    where m x = mapNames2 c f x

instance MapNames i1 (TiAssertion i1) i2 (TiAssertion i2) where
  mapNames2 = mapNames2Rec
instance MapNames i1 (TiPredicate i1) i2 (TiPredicate i2) where
  mapNames2 = mapNames2Rec

instance MapNames i1 (OTiAssertion i1) i2 (OTiAssertion i2) where
  mapNames2 c f@(vf,cf) (OA is ds pa) = OA is' ds' (m pa)
    where
       is' = map (vf (defval Pattern)) is
       ds' = [(vf (defval Local) i:>:m' t,m e)|(i:>:t,e)<-ds]
       m x = mapNames2 c f x
       m' x = mapNames2 Local f x

--------------------------------------------------------------------------------

instance MapDeclM (TiDecls i) (TiDecls i) where
  mapDeclM f (Decs ds dt) = flip Decs dt # mapDeclM f ds

instance MapDeclM (TiDecl i) (TiDecls i) where mapDeclM  = std_mapDeclM

instance MapDeclM (TiExp i) (TiDecls i) where
  mapDeclM f (Exp e) = Exp # mapDeclM f e
  mapDeclM f (TiTyped e t) = flip TiTyped t # mapDeclM f e
  mapDeclM f e@(TiSpec{}) = return e

instance MapDeclM (TiAssertion i) (TiDecls i) where mapDeclM = std_mapDeclM
instance MapDeclM (TiPredicate i) (TiDecls i) where mapDeclM = std_mapDeclM

instance MapDeclM (OTiAssertion i) (TiDecls i) where
  mapDeclM f (OA is ds pa) = OA is ds # mapDeclM f pa
