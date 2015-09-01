module RefacTypeSyn where

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

type SimpPos = (Int,Int) -- Line,col
