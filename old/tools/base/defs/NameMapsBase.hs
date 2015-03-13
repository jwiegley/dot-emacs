module NameMapsBase where
import NameMaps
import NameMapsBaseStruct()
import DefinedNamesBase() -- because of tp, grr
import Syntax
--import MUtils

instance AccNames i (HsDeclI i) where accNames = accNamesRec
instance AccNames i (HsExpI  i) where accNames = accNamesRec
instance AccNames i (HsPatI  i) where accNames = accNamesRec
instance AccNames i (HsTypeI i) where accNames = accNamesRec

instance MapNames i1 (HsDeclI i1) i2 (HsDeclI i2) where mapNames2 = mapNames2Rec
instance MapNames i1 (HsExpI  i1) i2 (HsExpI  i2) where mapNames2 = mapNames2Rec
instance MapNames i1 (HsPatI  i1) i2 (HsPatI  i2) where mapNames2 = mapNames2Rec
instance MapNames i1 (HsTypeI i1) i2 (HsTypeI i2) where mapNames2 = mapNames2Rec

instance (Monad m,Functor m) => SeqNames m (HsDeclI (m i)) (HsDeclI i) where
  seqNames = seqNamesRec
instance (Monad m,Functor m) => SeqNames m (HsExpI (m i)) (HsExpI i) where
  seqNames = seqNamesRec
instance (Monad m,Functor m) => SeqNames m (HsPatI (m i)) (HsPatI i) where
  seqNames = seqNamesRec
instance (Monad m,Functor m) => SeqNames m (HsTypeI (m i)) (HsTypeI i) where
  seqNames = seqNamesRec
