{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SyntaxRec(module SyntaxRec,module HasBaseStruct,module Recursive,module HsConstants) where
import Data.Maybe(fromMaybe)
import SrcLoc1
import BaseSyntax
import HasBaseStruct
import SpecialNames
import Recursive
import HsConstants(main_mod,main_name,mod_Prelude,is_unit_tycon_name)

import Data.Generics

-- Tie the recursive knots:

type BaseDeclI i
  = DI i
      (HsExpI i)
      (HsPatI i)
      [HsDeclI i] -- nested declarations
      (HsTypeI i) -- type expressions
      [HsTypeI i] -- contexts are lists of types
      (HsTypeI i) -- lhs of type defs

type BaseExpI i = EI i (HsExpI i) (HsPatI i) [HsDeclI i] (HsTypeI i) [HsTypeI i]
type BasePatI i = PI i (HsPatI i)
type BaseTypeI i = TI i (HsTypeI i)

newtype HsDeclI i = Dec (BaseDeclI i)   deriving (Ord,Read, Eq, Show, Data, Typeable)
newtype HsExpI i  = Exp (BaseExpI  i)   deriving (Ord, Read, Eq, Show, Data, Typeable)
newtype HsPatI i  = Pat (BasePatI  i)   deriving (Ord, Read, Eq, Show, Data, Typeable)
newtype HsTypeI i = Typ (BaseTypeI i)   deriving (Ord, Eq, Show ,Data, Typeable)
newtype HsKind    = Knd (K HsKind)      deriving (Ord,Eq, Show, Data, Typeable)

instance Rec (HsDeclI i) (BaseDeclI i)      where r = Dec; struct (Dec d) = d
instance Rec (HsExpI i)  (BaseExpI i)       where r = Exp; struct (Exp e) = e
instance Rec (HsPatI i)  (PI i (HsPatI i))  where r = Pat; struct (Pat p) = p
instance Rec (HsTypeI i) (TI i (HsTypeI i)) where r = Typ; struct (Typ t) = t
instance Rec HsKind      (K HsKind)         where r = Knd; struct (Knd k) = k

-- This makes all the convenience constructor functions available for
-- the base syntax (There is some overlap with the Rec class, but for
-- extensions to the syntax, base will be different from rec...):
instance HasBaseStruct (HsDeclI i) (BaseDeclI i)  where base = Dec
instance HasBaseStruct (HsExpI i)  (BaseExpI i)   where base = Exp
instance HasBaseStruct (HsPatI i)  (BasePatI i)   where base = Pat
instance HasBaseStruct (HsTypeI i) (BaseTypeI i)  where base = Typ
instance HasBaseStruct HsKind      (K HsKind)     where base = Knd

instance GetBaseStruct (HsDeclI i) (BaseDeclI i)  where
   basestruct = Just . struct

instance GetBaseStruct (HsPatI i) (BasePatI i) where
    basestruct = Just . struct

instance GetBaseStruct (HsExpI i) (BaseExpI i) where
  basestruct = Just . struct

instance HasSrcLoc (HsDeclI i) where srcLoc = srcLoc . struct



-- Module building
hsModule s m es (imp, decls) = HsModule s m es (reverse imp) (reverse decls)

-- An omitted module header is equivalent to module Main(main) where ...
hsMainModule loc body =
  hsModule loc (main_mod (srcFile loc)) (Just [exportVar main_name]) body

-- When consing a Decl onto a Decl list if the new Decl and the Decl on the
-- front of the list are for the same function, we can merge the Match lists
-- rather than just cons the new decl to the front of the list.
--funCons :: HsDecl -> [HsDecl] -> [HsDecl]
funCons (d1 @ (Dec (HsFunBind s1 m1)))
    (ds @ ((d2 @ (Dec (HsFunBind s2 m2))) : more)) =
    if same m1 m2
    then Dec (HsFunBind s2 (m2 ++ m1)) : more
    else d1 : ds
    where same ((HsMatch _ n1 _ _ _):_) ((HsMatch _ n2 _ _ _):_) = n1 == n2
          same _                        _                        = False
funCons d ds = d : ds


-- Exp building
hsVar name                  = HsVar name
hsCon name                  = HsCon name

--mkRecord :: HsExp -> [HsFieldUpdate HsExp] -> HsExp
mkRecord s (Exp (HsId (HsCon c))) fbinds = hsRecConstr s c fbinds
mkRecord s e                      fbinds = hsRecUpdate s e fbinds

-- Used to construct contexts in the parser
--tupleTypeToContext :: HsType -> [HsType]
tupleTypeToContext t = tupleTypeToContext' is_unit_tycon_name is_tuple_tycon_name t

tupleTypeToContext' is_unit_tycon_name is_tuple_tycon_name t =
    fromMaybe [t] (ctx t [])
  where
    ctx (Typ t) ts =
      case t of
        HsTyApp t1 t2 -> ctx t1 (t2:ts)
        HsTyCon c -> if if null ts
			then is_unit_tycon_name c
			else is_tuple_tycon_name (length ts-1) c
		     then Just ts
		     else Nothing
        _ -> Nothing


-- instance Show i => Show (HsTypeI i) where showsPrec p (Typ x) = (showsPrec p x)
instance Read i => Read (HsTypeI i) where
    readsPrec p s = [(Typ t,r)|(t,r)<-readsPrec p s]
