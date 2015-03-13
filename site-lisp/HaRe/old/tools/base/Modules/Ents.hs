{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Ents (module Ents, isValue) where

import TypedIds 
import HsIdent
import HsName(ModuleName)
import PosName(Id)

import Set60204
-- interface of the module system to the concrete type of entities

type Entity = Ent Id 

-- The type of entities
data Ent n = Ent ModuleName (HsIdentI n) (IdTy n) deriving (Show,Read)

instance Eq n => Eq (Ent n) where
  Ent m1 i1 t1 == Ent m2 i2 t2 = m1==m2 && i1==i2 && namespace t1==namespace t2

instance Ord n => Ord (Ent n) where
  compare (Ent m1 i1 t1) (Ent m2 i2 t2) =
     compare (m1,i1,namespace t1) (m2,i2,namespace t2)

instance HasNameSpace (Ent n) where namespace = namespace . idTy
instance HasIdTy n (Ent n) where idTy (Ent _ _ ty) = ty

isCon (Ent _ (HsCon _) x) 
  | not (isAssertion x)   = namespace x == ValueNames
isCon _                   = False
 
owns (Ent m (HsCon n) (Type tyinfo)) = fromListS $
  map (mkCons . conName) (constructors tyinfo) ++
  map mkFields (fields tyinfo)
  where
    mkCons c      = Ent m (HsCon c) (ConstrOf n tyinfo)
    mkFields f    = Ent m (HsVar f) (FieldOf n tyinfo)
 
owns (Ent m (HsCon n) (Class cnt xs)) = fromListS (cvt `map` xs)
  where
  cvt x = Ent m (HsVar x) (MethodOf n cnt xs)

owns _ = emptyS

