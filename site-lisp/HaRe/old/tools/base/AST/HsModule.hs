{-# LANGUAGE DeriveDataTypeable #-}
module HsModule(module HsModule,ModuleName(..)) where
import Data.List(sort,nub)
import SrcLoc1
import HsName(ModuleName(..))
import HsIdent(HsIdentI(..))
import HsConstants(mod_Prelude')

import Data.Generics

data HsModuleI m i ds
    = HsModule { hsModSrcLoc  :: SrcLoc,
		 hsModName    :: m,
		 hsModExports :: Maybe [HsExportSpecI m i],
		 hsModImports :: [HsImportDeclI m i],
		 hsModDecls   :: ds }
      deriving (Eq, Show, Data, Typeable)

instance HasSrcLoc (HsModuleI m i ds) where srcLoc = hsModSrcLoc

data HsExportSpecI m i
    = EntE (EntSpec i)          -- only unqualified names allowed for i
    | ModuleE m                 -- module M
    deriving (Eq, Show, Data, Typeable)

data HsImportDeclI m i
    = HsImportDecl SrcLoc m {-qualified-} Bool {-as-} (Maybe m)
                  (Maybe (ImpSpec i))
      deriving (Eq, Show, Data, Typeable)
type ImpSpec i = ({-hiding-}Bool, [EntSpec i])

--hsImpFrom :: HsImportDecl -> ModuleName
hsImpFrom (HsImportDecl _ x _ _ _)  = x
hsModImportsFrom m = sort . nub . map hsImpFrom . hsModImports $ m

type HsImportSpecI i = EntSpec i -- qualified names allowed for i

data EntSpec i
    = Var i                   -- x (a variable identifier)
    | Abs i                   -- T, C (or P-Logic assertion/predicate)
    | AllSubs i               -- T(..), C(..)
    | ListSubs i [HsIdentI i] -- T(C_1, ..., C_n, f_1, ..., f_n)
                              -- C(m_1, ..., m_2)
    deriving (Eq, Show, Data, Typeable)

exportVar = EntE . Var

--------------------------------------------------------------------------------

--Functions for making the implicit import of Prelude explicit:

optAddPrelude sn prel = if prel then addPrelude sn else id

addPrelude sn m@HsModule{hsModImports=is} = m{hsModImports=prelimps++is}
  where
    prelimps = prelqual:if sn mod_Prelude' `elem` map hsImpFrom is
			then []
			else [prelunqual]

    prelqual = prel True
    prelunqual = prel False
    prel qual = HsImportDecl loc0 (sn mod_Prelude') qual Nothing Nothing
    
