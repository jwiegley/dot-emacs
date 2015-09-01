{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
module PNT where

import HsName
import HsIdent
import UniqueNames(PN,OptSrcLoc(..),HasOrig(..))
import TypedIds(IdTy,HasIdTy(..))

import SrcLoc1(HasSrcLoc(..))
import HasBaseName(HasBaseName(..))
import QualNames(QualNames(..),unqual)
import PrettyPrint(Printable(..),PrintableOp(..))

import Data.Generics


type PName = PN HsName
type PIdent = HsIdentI PName
type PId = PN Id

data PNT = PNT PName (IdTy PId) OptSrcLoc deriving (Show,Read, Data, Typeable)

instance Eq  PNT where PNT i1 _ _ == PNT i2 _ _ = i1==i2
instance Ord PNT where compare (PNT i1 _ _) (PNT i2 _ _) = compare i1 i2
instance HasOrig PNT where orig (PNT pn _ _)  = orig pn
instance HasOrig i => HasOrig (HsIdentI i) where orig = orig . getHSName

instance HasIdTy PId PNT where idTy (PNT _ ty _) = ty


--instance HasNameSpace PNT where namespace (PNT _ idty _) = namespace idty
--instance HasNameSpace i => HasNameSpace (HsIdentI i) where
--   namespace = namespace . getHSName


instance QualNames qn m n => QualNames (PN qn) m (PN n) where
    getQualifier                = getQualifier . getBaseName
    getQualified                = fmap getQualified

    mkUnqual                    = fmap mkUnqual
    mkQual m                    = fmap (mkQual m)

instance Printable PNT where
  ppi (PNT i _ _) = ppi i
  wrap  (PNT i _ _) = wrap i

instance PrintableOp PNT where
  isOp (PNT i _ _) = isOp i
  ppiOp (PNT i _ _) = ppiOp i

--instance Unique (PN i) where unique m (PN _ o) = o

instance HasBaseName PNT HsName where
  getBaseName (PNT i _ _) = getBaseName i

instance QualNames PNT ModuleName PNT where
    getQualifier                = getQualifier . getBaseName
    getQualified (PNT i t p)    = PNT (unqual i) t p -- hmm

    mkUnqual                    = id -- hmm
    mkQual m (PNT i t p)        = PNT (mkQual m (getQualified i)) t p

instance HasSrcLoc PNT where
  srcLoc (PNT i _ (N (Just s))) = s
  srcLoc (PNT i _ _) = srcLoc i -- hmm
