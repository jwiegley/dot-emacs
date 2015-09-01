{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module GhcRefacTypeSyn where


-- Modules from GHC
import qualified GHC     as GHC
import qualified HsExpr  as GHC
import qualified RdrName as GHC
import qualified SrcLoc  as GHC


import Data.Generics
import SrcLoc1

{-
--Modules from Programatic: 
import PosSyntax
import ScopeModule
import HsName hiding (ModuleName)
import PNT
import Ents
import PosName 
import Relations
import Names

data NameSpace = ValueName | ClassName | TypeCon | DataCon | Other  deriving (Eq, Show)

type HsDeclP   =HsDeclI PNT
type HsPatP    =HsPatI PNT
type HsExpP    =HsExpI PNT
-}
type HsExpP    = GHC.HsExpr GHC.RdrName
{-
type HsMatchP  =HsMatchI PNT (HsExpP) (HsPatP) [HsDeclP]
-- type HsModuleP =HsModuleI (SN HsName.HsName) [HsDeclI PNT]  
type HsModuleP =HsModuleI ModuleName PNT [HsDeclI PNT]  
type HsImportDeclP=HsImportDeclI ModuleName PNT -- (SN HsName.HsName)
type HsExportEntP = HsExportSpecI ModuleName PNT
type RhsP      =HsRhs HsExpP 
type GuardP    =(SrcLoc, HsExpP, HsExpP)
type HsAltP    =HsAlt HsExpP HsPatP [HsDeclP]
--type HsConDeclP=HsConDeclI PNT (HsTypeI PNT)
type HsStmtP   =HsStmt HsExpP HsPatP [HsDeclP]
type HsStmtAtomP = HsStmtAtom HsExpP HsPatP [HsDeclP]
type HsFieldP  =HsFieldI PNT HsExpP
type HsTypeP   = HsTypeI PNT 
type EntSpecP  = EntSpec PNT
type HsConDeclP = HsConDeclI PNT HsTypeP [HsTypeP]
type HsConDeclP' = HsConDeclI PNT (TI PNT HsTypeP) [TI PNT HsTypeP]
type ENT =Ents.Ent PosName.Id
type InScopes=((Relations.Rel Names.QName (Ents.Ent PosName.Id)))

type Exports =[(PosName.Id, Ent PosName.Id)]
-}
type SimpPos = (Int,Int) -- Line, column 

-- Additions for GHC
type PosToken = (GHC.Located GHC.Token, String)

data Pos = Pos { char, line, column :: !Int } deriving (Show)
-- it seems that the field char is used to handle special characters including the '\t'

type HsName = GHC.RdrName
type PN     = GHC.RdrName

type HsModuleP = GHC.HsModule GHC.RdrName


-- ----------------------------------------------------
-- From PNT

type PName  = HsName
{-
type PIdent = HsIdentI PName
type PId    = PN Id
-}
--data PNT = PNT PName (IdTy PId) OptSrcLoc deriving (Show,Read, Data, Typeable)
data PNT = PNT PName OptSrcLoc deriving (Data, Typeable)

instance Eq  PNT where PNT i1 _  == PNT i2 _  = i1==i2
instance Ord PNT where compare (PNT i1 _) (PNT i2 _) = compare i1 i2
-- instance HasOrig PNT where orig (PNT pn _ _)  = orig pn
-- instance HasOrig i => HasOrig (HsIdentI i) where orig = orig . getHSName

-- instance HasIdTy PId PNT where idTy (PNT _ ty _) = ty


--instance HasNameSpace PNT where namespace (PNT _ idty _) = namespace idty
--instance HasNameSpace i => HasNameSpace (HsIdentI i) where
--   namespace = namespace . getHSName

{-
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

-}

------------------------------------------------------------------------
-- From UniqueNames

-- type SrcLoc = GHC.SrcSpan

newtype OptSrcLoc = N (Maybe SrcLoc) deriving (Data, Typeable)
noSrcLoc = GHC.noSrcSpan
srcLoc = N . Just
optSrcLoc = N
instance Eq  OptSrcLoc where _ == _ = True
instance Ord OptSrcLoc where compare _ _ = EQ

