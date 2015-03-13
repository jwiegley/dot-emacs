{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This is a legacy module from the pre-GHC HaRe, and will disappear
-- eventually.

module Language.Haskell.Refact.Utils.TypeSyn where


-- Modules from GHC
import qualified GHC        as GHC
import qualified Name       as GHC
import qualified Outputable as GHC

type HsExpP    = GHC.HsExpr GHC.RdrName
type HsPatP    = GHC.Pat GHC.RdrName
type HsDeclP   = GHC.LHsDecl GHC.RdrName

type HsDeclsP = GHC.HsGroup GHC.Name

-- type InScopes=((Relations.Rel Names.QName (Ents.Ent PosName.Id)))
type InScopes = [GHC.Name]

-- Additions for GHC
type PosToken = (GHC.Located GHC.Token, String)

type Export = GHC.LIE GHC.RdrName

-- ---------------------------------------------------------------------
-- From old/tools/base/defs/PNT.hs

-- | HsName is a name as it is found in the source
-- This seems to be quite a close correlation
type HsName = GHC.RdrName

-- |The PN is the name as it occurs to the parser, and
-- corresponds with the GHC.RdrName
-- type PN     = GHC.RdrName
newtype PName = PN HsName deriving (Eq)

-- | The PNT is the unique name, after GHC renaming. It corresponds to
-- GHC.Name data PNT = PNT GHC.Name deriving (Data,Typeable) -- Note:
-- GHC.Name has SrcLoc in it already

instance Show GHC.NameSpace where
  show ns
    | ns == GHC.tcName   = "TcClsName"
    | ns == GHC.dataName = "DataName"
    | ns == GHC.varName  = "VarName"
    | ns == GHC.tvName   = "TvName"
    | otherwise          = "UnknownNamespace"

instance GHC.Outputable GHC.NameSpace where
  ppr x = GHC.text $ show x

instance GHC.Outputable (GHC.MatchGroup GHC.Name) where
  ppr (GHC.MatchGroup ms _ptctyp) = GHC.text "MatchGroup" GHC.<+> GHC.ppr ms


instance GHC.Outputable (GHC.Match GHC.Name) where
  ppr (GHC.Match pats mtyp grhs) = GHC.text "Match" GHC.<+> GHC.ppr pats
                                                    GHC.<+> GHC.ppr mtyp
                                                    GHC.<+> GHC.ppr grhs


instance GHC.Outputable (GHC.GRHSs GHC.Name) where
  ppr (GHC.GRHSs grhss binds) = GHC.text "GRHSs" GHC.<+> GHC.ppr grhss
                                                 GHC.<+> GHC.ppr binds


instance GHC.Outputable (GHC.GRHS GHC.Name) where
  ppr (GHC.GRHS guards rhs) = GHC.text "GRHS" GHC.<+> GHC.ppr guards
                                              GHC.<+> GHC.ppr rhs


instance GHC.Outputable (GHC.HsTupArg GHC.Name) where
  ppr (GHC.Present e)    = GHC.text "Present" GHC.<+> GHC.ppr e
  ppr (GHC.Missing _typ) = GHC.text "Missing"


instance GHC.Outputable (GHC.ConDeclField GHC.Name) where
  ppr (GHC.ConDeclField name typ doc) = GHC.text "ConDeclField"
                                          GHC.<+> GHC.ppr name
                                          GHC.<+> GHC.ppr typ
                                          GHC.<+> GHC.ppr doc


-- ---------------------------------------------------------------------

-- type HsModuleP = GHC.Located (GHC.HsModule GHC.RdrName)

-- ---------------------------------------------------------------------
