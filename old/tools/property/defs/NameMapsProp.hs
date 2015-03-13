module NameMapsProp where
import NameMaps
import NameMapsPropStruct()
import NameMapsBaseStruct()
import NameMapsBase()
import PropSyntax
--import MUtils

instance AccNames i (HsExpI i) where accNames = accNamesRec
instance AccNames i (HsDeclI i) where accNames = accNamesRec
instance AccNames i (AssertionI i) where accNames = accNamesRec
instance AccNames i (PredicateI i) where accNames = accNamesRec

instance MapNames i1 (HsDeclI i1) i2 (HsDeclI i2) where mapNames2 = mapNames2Rec
instance MapNames i1 (HsExpI  i1) i2 (HsExpI  i2) where mapNames2 = mapNames2Rec
instance MapNames i1 (AssertionI i1) i2 (AssertionI i2) where mapNames2 = mapNames2Rec
instance MapNames i1 (PredicateI i1) i2 (PredicateI i2) where mapNames2 = mapNames2Rec

instance (Monad m,Functor m) => SeqNames m (HsDeclI (m i)) (HsDeclI i) where
  seqNames = seqNamesRec
instance (Monad m,Functor m) => SeqNames m (HsExpI (m i)) (HsExpI i) where
  seqNames = seqNamesRec
instance (Monad m,Functor m) => SeqNames m (AssertionI (m i)) (AssertionI i) where
  seqNames = seqNamesRec
instance (Monad m,Functor m) => SeqNames m (PredicateI (m i)) (PredicateI i) where
  seqNames = seqNamesRec

instance (MapNames i1 b1 i2 b2,MapNames i1 p1 i2 p2)
      => MapNames i1 (Prop b1 p1) i2 (Prop b2 p2)
  where mapNames2 d f = mapProp (mapNames2 d f) (mapNames2 d f)

instance (SeqNames m b1 b2,SeqNames m p1 p2)
       => SeqNames m (Prop b1 p1) (Prop b2 p2) where
  seqNames = seqProp . mapProp seqNames seqNames

