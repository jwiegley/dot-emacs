
module PropSyntaxRec(
  module PropSyntaxRec,
  module HasBaseStruct,
  module HasPropStruct,
  module Syntax
 ) where

import List
import PropSyntaxStruct
import HasBaseStruct
import HasPropStruct
import PrettyPrint
--import SrcLoc
import SpecialNames
--import ToHaskell(toHaskell)
-- Some things from the base syntax are reused unchanged:
import Syntax(HsPatI(..),
              HsTypeI(..),HsKind(..),Rec(..),HsModuleI(..),
	      HsName,ModuleName(..),Id,HsIdentI(..),HsFieldI(..),
	      hsModule,tupleTypeToContext',hsVar,hsCon)


-- Tie the recursive knots
newtype HsDeclI i = Dec {unDec::PropDecl i} deriving (Eq, Show)
newtype AssertionI i = PA {unPA::PropPA i} deriving (Eq, Show)
newtype PredicateI i = PP {unPP::PropPP i} deriving (Eq, Show)
newtype HsExpI i  = Exp {unExp::PropExp  i} deriving (Eq, Show)

-- Recursion:
instance Rec (HsDeclI i)    (PropDecl i) where rec=Dec; struct=unDec
instance Rec (AssertionI i) (PropPA i)   where rec=PA; struct=unPA
instance Rec (PredicateI i) (PropPP i)   where rec=PP; struct=unPP
instance Rec (HsExpI  i) (PropExp  i) where rec=Exp; struct=unExp

instance HasPropStruct (HsDeclI i) (PD i (AssertionI i) (PredicateI i))
   where proprec=rec . Prop
instance HasPropStruct (AssertionI i) (PropPA i)   where proprec=rec
instance HasPropStruct (PredicateI i) (PropPP i)   where proprec=rec
instance HasPropStruct (HsExpI  i)    (PropExp  i) where proprec=rec

instance GetPropStruct (HsDeclI i) (PD i (AssertionI i) (PredicateI i)) where
  propstruct = propstruct . struct

-- Structure:
type HsQualTypeI i = Q [HsTypeI i] (HsTypeI i)

type PropDecl i =
  PropDI i (HsExpI i) (HsPatI i) [HsDeclI i] (HsTypeI i) [HsTypeI i] (HsTypeI i) (AssertionI i) (PredicateI i)
type PropPA i = PA i (HsExpI i) (HsQualTypeI i) (AssertionI i) (PredicateI i)
type PropPP i = PP i (HsExpI i) (HsPatI i) (HsQualTypeI i) (AssertionI i) (PredicateI i)

type PropExp i = BaseExp i

-- Base structure:
type BaseDecl i = DI i (HsExpI i) (HsPatI i) [HsDeclI i] (HsTypeI i) [HsTypeI i] (HsTypeI i)
type BaseExp i = EI i (HsExpI i) (HsPatI i) [HsDeclI i] (HsTypeI i) [HsTypeI i]

{-
type BasePat i = PI i (HsPatI i)
-}

-- This makes all the convenience constructor functions for the base syntax
-- available also for the extended syntax:
instance HasBaseStruct (HsDeclI i) (BaseDecl i) where base = rec . base
instance GetBaseStruct (HsDeclI i) (BaseDecl i) where basestruct = basestruct . struct
instance HasBaseStruct (HsExpI  i) (BaseExp  i) where base = rec
instance GetBaseStruct (HsExpI  i) (BaseExp  i) where basestruct = Just . struct

{-
instance HasBaseStruct (HsPatI  i) (BasePat  i) where base = rec . base
instance GetBaseStruct (HsPatI  i) (BasePat  i) where basestruct = basestruct . struct
-}

--type HsModuleR = HsModuleI HsName [HsDecl]
--type HsStmtR   = HsStmt HsExp HsPat [HsDecl]
--type HsAltR    = HsAlt HsExp HsPat [HsDecl]


instance (IsSpecialName i,PrintableOp i) => Printable (HsDeclI i) where
    ppi = recprop ppi ({-property .-} ppi)
    wrap = recprop wrap ({-property .-} wrap)

    ppiList [] = empty
    ppiList ds = vcat $ (map (blankline . ppi) (init ds)) ++ [ppi (last ds)]

instance (IsSpecialName i,PrintableOp i) => Printable (HsExpI i) where
  ppi = ppi . struct; wrap = wrap . struct

instance (IsSpecialName i,PrintableOp i) => Printable (AssertionI i) where
  ppi = ppi . struct; wrap = wrap . struct

instance (IsSpecialName i,PrintableOp i) => Printable (PredicateI i) where
  ppi = ppi . struct; wrap = wrap . struct

instance HasSrcLoc (HsDeclI i) where srcLoc = srcLoc . struct

-- When consing a Decl onto a Decl list if the new Decl and the Decl on the
-- front of the list are for the same function, we can merge the Match lists
-- rather than just cons the new decl to the front of the list.
--funCons :: HsDecl -> [HsDecl] -> [HsDecl]
funCons (d1 @ (Dec (Base (HsFunBind s1 m1))))
	(ds @ ((d2 @ (Dec (Base (HsFunBind s2 m2)))) : more)) =
    if same m1 m2
    then hsFunBind s1 (m2 ++ m1) : more
    else d1 : ds
    where same ((HsMatch _ n1 _ _ _):_) ((HsMatch _ n2 _ _ _):_) = n1 == n2
	  same _                        _                        = False
funCons d ds = d : ds

--mkRecord :: HsExp -> [HsFieldUpdate HsExp] -> HsExp
mkRecord s (Exp (HsId (HsCon c))) fbinds = hsRecConstr s c fbinds
mkRecord s e                      fbinds = hsRecUpdate s e fbinds

--property d = if toHaskell then comment d else d

comment d = text "{-"
            $$ blankline d
            $$ text "-}"
