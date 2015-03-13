{-# LANGUAGE DeriveDataTypeable  #-}
module HsIdent where
import SrcLoc1
import Data.Generics

data HsIdentI i
    = HsVar i
    | HsCon i
      deriving (Eq, Ord, Show,Read, Data, Typeable)

-- This is perhaps not a good idea, in case we want to change HsIdentI...
instance Functor HsIdentI where fmap = mapHsIdent

getHSName = accHsIdent id

mapHsIdent nf = mapHsIdent2 nf nf

mapHsIdent2 vf cf = accHsIdent2 (HsVar . vf) (HsCon . cf)

accHsIdent nf = accHsIdent2 nf nf

accHsIdent2 vf cf (HsVar n) = vf n
accHsIdent2 vf cf (HsCon n) = cf n

seqHsIdent (HsVar i)    = fmap HsVar i
seqHsIdent (HsCon i)    = fmap HsCon i

isHsVar (HsVar _) = True
isHsVar  _        = False

isHsCon (HsCon _) = True
isHsCon  _        = False

{- -- not used
hsVarName (HsVar v) = Just v
hsVarName _ = Nothing

hsConName (HsCon c) = Just c
hsConName _ = Nothing
-}

---
instance HasSrcLoc i => HasSrcLoc (HsIdentI i) where
  srcLoc = srcLoc . getHSName
