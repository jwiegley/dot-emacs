module NameMapsPropStruct where
import NameMaps
import PropSyntaxStruct
import MUtils

instance (AccNames i e,AccNames i t,AccNames i pa,AccNames i pp)
      => AccNames i (PA i e t pa pp) where
  accNames f = accPA f a a a a
    where a x = accNames f x

instance (AccNames i e,AccNames i p,AccNames i t,AccNames i pa,AccNames i pp)
       => AccNames i (PP i e p t pa pp) where
  accNames f = accPP f a a a a a
    where a x = accNames f x

instance (AccNames i pa,AccNames i pp) => AccNames i (PD i pa pp) where
  accNames f = accPD f a a
    where a x = accNames f x

instance (MapNames i1 e1 i2 e2, MapNames i1 t1 i2 t2,
          MapNames i1 pa1 i2 pa2, MapNames i1 pp1 i2 pp2)
      => MapNames i1 (PA i1 e1 t1 pa1 pp1) i2 (PA i2 e2 t2 pa2 pp2) where
  mapNames2 d f@(vf,cf) pa =
      case pa of
        Quant q i optt pa -> Quant q (vf (defval Local) i) (ml # optt) (m pa)
        _ -> mapPA2 undefined (cf logic) m ml m m pa
    where
      m x = m' d x
      ml x = m' Local x
      m' dctx = mapNames2 dctx f

logic = (Logic,ValueNames)

instance (MapNames i1 e1 i2 e2, MapNames i1 p1 i2 p2, MapNames i1 t1 i2 t2,
          MapNames i1 pa1 i2 pa2, MapNames i1 pp1 i2 pp2)
      => MapNames i1 (PP i1 e1 p1 t1 pa1 pp1) i2 (PP i2 e2 p2 t2 pa2 pp2) where
  mapNames2 d f@(vf,cf) =
      mapPP2 undefined (cf logic) m m ml m m
    where
      m x = m' d x
      ml x = m' Local x
      m' dctx = mapNames2 dctx f

instance (MapNames i1 pa1 i2 pa2, MapNames i1 pp1 i2 pp2)
      => MapNames i1 (PD i1 pa1 pp1) i2 (PD i2 pa2 pp2) where
  mapNames2 d f@(vf,cf) pd =
      case pd of
        HsAssertion s optn a -> HsAssertion s (cf (defval d) # optn) (m a)
        HsPropDecl s n ns p -> HsPropDecl s (cf (defval d) n) (map dp ns) (m p)
    where
      m x = mapNames2 d f x
      dp = both (Def Pattern,ValueNames) mapHsIdent2 f

instance (SeqNames m e1 e2,SeqNames m t1 t2,
	  SeqNames m pa1 pa2,SeqNames m pp1 pp2)
      => SeqNames m (PA (m i) e1 t1 pa1 pp1) (PA i e2 t2 pa2 pp2) where
  seqNames = seqPA . mapPA id seqNames seqNames seqNames seqNames

instance (SeqNames m e1 e2,SeqNames m p1 p2,SeqNames m t1 t2,
	  SeqNames m pa1 pa2,SeqNames m pp1 pp2)
      => SeqNames m (PP (m i) e1 p1 t1 pa1 pp1) (PP i e2 p2 t2 pa2 pp2) where
  seqNames = seqPP . mapPP id seqNames seqNames seqNames seqNames seqNames

instance (SeqNames m pa1 pa2,SeqNames m pp1 pp2)
      => SeqNames m (PD (m i) pa1 pp1) (PD i pa2 pp2) where
  seqNames = seqPD . mapPD id seqNames seqNames

---

instance (SeqNames m c1 c2,SeqNames m t1 t2)
      => SeqNames m (Q c1 t1) (Q c2 t2) where
   seqNames (c:=>t) = (:=>) # seqNames c <# seqNames t

instance (MapNames i1 c1 i2 c2,MapNames i1 t1 i2 t2)
      => MapNames i1 (Q c1 t1) i2 (Q c2 t2) where
   mapNames2 d f (c:=>t) = m c:=>m t
      where m x = mapNames2 d f x
