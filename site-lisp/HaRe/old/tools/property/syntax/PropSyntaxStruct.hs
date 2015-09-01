module PropSyntaxStruct (module PropSyntaxStruct,module P) where

import BaseSyntax as P
import HsPropStruct as P
import HsPropMaps as P
import HsPropPretty
import HasBaseStruct 
import HasPropStruct
import NameMaps
import PrettyPrint
import HsDeclPretty(ppContext)
import SrcLoc
import MUtils
import MapDeclM
import Recursive(struct)

data Q c t = c:=>t deriving (Eq,Show)

--type PropEI i e p ds t c = EI i e p ds t c
type PropDI i e p ds t c tp pa pp = Prop (DI i e p ds t c tp) (PD i pa pp)

data Prop b p = Base b | Prop p deriving (Eq,Show)

prop bf pf (Base b) = bf b
prop bf pf (Prop p) = pf p

recprop f g = prop f g . struct

mapProp bf pf = prop (Base . bf) (Prop . pf)
mapMProp bf pf = prop (fmap Base . bf) (fmap Prop . pf)
mapBase f = mapProp f id
isBase p = prop p (const False)
maybeBase f = prop f (const Nothing)
maybeProp = prop (const Nothing)
listBase f = prop f (const [])

seqProp (Base b) = Base # b
seqProp (Prop p) = Prop # p

instance HasBaseStruct (Prop b p) b where base = Base
instance GetBaseStruct (Prop b p) b where basestruct = maybeBase Just
instance HasPropStruct (Prop b p) p where proprec = Prop
instance GetPropStruct (Prop b p) p where propstruct = maybeProp Just

--------------------------------------------------------------------------------

instance (AccNames i b,AccNames i p) => AccNames i (Prop b p) where
  accNames f = prop (accNames f) (accNames f)

instance (AccNames i c,AccNames i t) => AccNames i (Q c t) where
  accNames f (c:=>t) = accNames f c . accNames f t

--------------------------------------------------------------------------------

instance (HasSrcLoc b,HasSrcLoc p) => HasSrcLoc (Prop b p) where
  srcLoc = prop srcLoc srcLoc

instance (MapDeclM b ds,MapDeclM p ds) => MapDeclM (Prop b p) ds where
    mapDeclM f = mapMProp (mapDeclM f) (mapDeclM f)

instance (Printable b,Printable p) => Printable (Prop b p) where
  ppi = prop ppi ppi
  wrap = prop wrap wrap

instance (Printable c,Printable t) => Printable (Q c t) where
  ppi (c:=>t) = ppContext (ppis c)<+>t

