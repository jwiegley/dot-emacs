module NameMapsDecorate where
import NameMaps
import TiDecorate
import TiTypes
import TiKinds
--import NameMapsBase(bothtype,bothval)
import HsIdent(mapHsIdent2)
import HsDeclMaps(mapFunDeps)
import MapDeclM
import MapDeclMBaseStruct()
import MUtils

instance AccNames i (TiDecls i) where
  accNames f (Decs ds (ks,ts)) = accNames f ds . accNames f ts -- hmm, ks?

instance AccNames i (TiDecl i) where
  accNames f (Dec d) = accNames f d

instance AccNames i (TiExp i) where
  accNames f (Exp e) = accNames f e
  accNames f (TiSpec i _ ts) = accNames f i . accNames f ts
  accNames f (TiTyped e t) = a e . a t
    where a x = accNames f x

instance AccNames i (TiPat i) where
  accNames f (Pat p) = accNames f p
  accNames f (TiPApp p1 p2) = accNames f p1 . accNames f p2
  accNames f (TiPSpec i _ ts) = accNames f i . accNames f ts
  accNames f (TiPTyped p t) = accNames f p . accNames f t

instance AccNames i t => AccNames i (Typing x t) where
  accNames f (x:>:t) = accNames f t -- hmm, x?

instance AccNames i (Scheme i) where
  accNames f (Forall _ _ qt) = accNames f qt

instance AccNames i t => AccNames i (Qual i t) where
  accNames f (ps:=>t) = accNames f ps . accNames f t
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

instance MapNames i1 (TiPat i1) i2 (TiPat i2) where
  mapNames2 c f (Pat p) = Pat (mapNames2 c f p)
  mapNames2 c f (TiPApp p1 p2) = TiPApp (mapNames2 c f p1) (mapNames2 c f p2)
  mapNames2 c f (TiPSpec i sc ts) =
      TiPSpec (bothval mapHsIdent2 f i) (mapNames2 c f sc) (mapNames2 c f ts)
  mapNames2 c f (TiPTyped p t) = TiPTyped (mapNames2 c f p) (mapNames2 c f t)

instance MapNames i1 (Scheme i1) i2 (Scheme i2) where
  mapNames2 c f (Forall as vs qt) =
      Forall (mktvs f as) (mktvs f vs) (mapNames2 c f qt)

mtvs (vf,_) = map (vf (Def Local,ClassOrTypeNames))
mktvs (vf,_) = map (emap (vf (Def Local,ClassOrTypeNames)))

mts c f = map mt
  where mt (i:>:t) = bothval mapHsIdent2 f i:>:mapNames2 c f t

instance MapNames i1 (TypeInfo i1) i2 (TypeInfo i2) where
  mapNames2 c f ti =
      case ti of
        Data -> Data
        Newtype -> Newtype
        Class ps vs fdeps as ->
          Class (m ps) (mktvs f vs) ({-mapFunDeps tvarf-} fdeps) (mts c f as)
        Synonym vs t -> Synonym (mtvs f vs) (m t)
        Tyvar -> Tyvar
    where
      m x = mapNames2 c f x
      tvarf = fst f usetype


instance MapNames i1 t1 i2 t2
      => MapNames i1 (Qual i1 t1) i2 (Qual i2 t2) where
  mapNames2 c f (ps:=>t) = m ps:=>m t
    where m x = mapNames2 c f x

{-
instance MapNames i1 Kind i2 Kind where
  mapNames2 c f k = k
  mapNames f k = k
-}
--------------------------------------------------------------------------------

instance MapDeclM (TiDecls i) (TiDecls i) where
  mapDeclM f (Decs ds dt) = flip Decs dt # mapDeclM f ds

instance MapDeclM (TiDecl i) (TiDecls i) where mapDeclM  = std_mapDeclM

instance MapDeclM (TiExp i) (TiDecls i) where
  mapDeclM f (Exp e) = Exp # mapDeclM f e
  mapDeclM f (TiTyped e t) = flip TiTyped t # mapDeclM f e
  mapDeclM f e@(TiSpec{}) = return e

