{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module NameMaps(module NameMaps,NameSpace(..)) where
--import StateM
import MUtils
import Recursive
import AccList
import HsName(ModuleName)
import TypedIds(NameSpace(..))

class AccNames i s | s->i where
  accNames :: (i->a->a)->s->a->a

-- Auxiliary types for the MapNames class:

data Context i = TopLevel | Local | ClassDef i | Instance i | Pattern
               | Export | Import ModuleName
               --deriving (Show)

data Role i = Def (Context i) | Sig (Context i) | Use | Logic | FieldLabel
            | ExpEnt (Maybe i)  --Just i=subordinate to i
            | ImpEnt ModuleName (Maybe i)  --Just i=subordinate to i
            --deriving (Show)

type Occurence i = (Role i,NameSpace)

instance Functor Context where
  fmap f c = case c of
	       TopLevel -> TopLevel
	       Local -> Local
	       ClassDef i -> ClassDef (f i)
	       Instance i -> Instance (f i)
	       Pattern -> Pattern

instance Functor Role where
  fmap f (Def c) = Def (fmap f c)
  fmap f (Sig c) = Sig (fmap f c)
  fmap f Use = Use
  fmap f Logic = Logic
  fmap f FieldLabel = FieldLabel
  fmap f (ExpEnt opti) = ExpEnt (fmap f opti)
  fmap f (ImpEnt m opti) = ImpEnt m (fmap f opti)

class MapNames i1 s1 i2 s2 | s1->i1,s1 i2->s2,s2->i2 where
  mapNames2 :: Context i1 ->
               (Occurence i1->i1->i2,Occurence i1->i1->i2) -> s1 -> s2
            -- (variables           ,constructors        )
  mapNames :: (i1->i2) -> s1 -> s2
  mapNames f = mapNames2 TopLevel (const f,const f)

class (Monad m,Functor m) => SeqNames m s1 s2 | s1->m s2 where
  seqNames :: s1 -> m s2

instance AccNames i s => AccNames i [s] where
  accNames = accList . accNames

instance (AccNames i a,AccNames i b) => AccNames i (a,b) where
  accNames f (a,b) = accNames f a . accNames f b

instance (AccNames i a,AccNames i b,AccNames i c) => AccNames i (a,b,c) where
  accNames f (a,b,c) = accNames f a . accNames f b . accNames f c

instance MapNames i1 s1 i2 s2 => MapNames i1 [s1] i2 [s2] where
  mapNames2 dctx = map . mapNames2 dctx
  mapNames = map . mapNames

instance MapNames i1 s1 i2 s2 => MapNames i1 (Maybe s1) i2 (Maybe s2) where
  mapNames2 dctx = fmap . mapNames2 dctx
  mapNames = fmap . mapNames

instance (MapNames i1 a1 i2 a2,MapNames i1 b1 i2 b2)
      => MapNames i1 (a1,b1) i2 (a2,b2) where
  mapNames2 dctx f (a,b) = (mapNames2 dctx f a,mapNames2 dctx f b)
  mapNames f (a,b) = (mapNames f a,mapNames f b)

instance SeqNames m s1 s2 => SeqNames m [s1] [s2] where
  seqNames = mapM seqNames

instance SeqNames m s1 s2 => SeqNames m (Maybe s1) (Maybe s2) where
  seqNames = seqMaybe . fmap seqNames

instance (SeqNames m a1 a2,SeqNames m b1 b2)
      => SeqNames m (a1,b1) (a2,b2) where
  seqNames (a1,a2) = (,) # seqNames a1 <# seqNames a2

accNamesRec f = accNames f . struct
mapNames2Rec dctx f = r . mapNames2 dctx f . struct
seqNamesRec x = r # seqNames (struct x)

mapNamesM f = seqNames . mapNames f
mapNames2M ctx f = seqNames . mapNames2 ctx f

--- utilities

pat ctx g (vf,cf) = g (vf (defval ctx)) (cf useval)
bothval = both  useval
bothtype = both (Use,ClassOrTypeNames)
both x g (f1,f2) = g (f1 x) (f2 x)
useval=(Use,ValueNames)
usetype=(Use,ClassOrTypeNames)
defval ctx=(Def ctx,ValueNames)
sigval ctx=(Sig ctx,ValueNames)
deftype ctx=(Def ctx,ClassOrTypeNames)
