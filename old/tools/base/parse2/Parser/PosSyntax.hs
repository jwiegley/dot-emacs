module PosSyntax(module PosSyntax,module PosName,module Hs,SN) where
import Syntax hiding (ModuleName,HsName,Id,hsMainModule,hsTyTuple,main_name,is_unit_tycon_name,tupleTypeToContext)
import qualified Syntax as Hs hiding (ModuleName,HsName,Id,hsTyTuple)
import HsConstants(main_mod,tuple,mod_Prelude')
import qualified HsConstants as Hs
--import PrettyPrint
import SourceNames
import PosName
--import SpecialNames
import QualNames(isQual)
-- import Entity

pos i p = SN i p

type HsExp = HsExpI HsName
type HsPat = HsPatI HsName
type HsDecl = HsDeclI HsName
type HsType = HsTypeI HsName

type HsField = HsFieldI HsName
type HsImportDecl = HsImportDeclI ModuleName HsName
type HsConDecl = HsConDeclI HsName
type HsExportSpec = HsExportSpecI ModuleName HsName
type HsImportSpec = HsImportSpecI HsName
type HsModuleR = HsModuleI ModuleName HsName [HsDecl]

qualid (p,s) = pos (splitQualName (srcFile p) s) p

unqualid (p,s) = pos (UnQual s) p

qualify m n = pos (Qual m n)

tuple_con_name arity = qualify mod_Prelude' $ tuple arity
unit_tycon_name = pos Hs.unit_tycon_name
list_tycon_name = qualify mod_Prelude' "[]"
fun_tycon_name = qualify mod_Prelude' "->"
tuple_tycon_name arity = tuple_con_name arity

list_tycon = hsTyCon . list_tycon_name :: SrcLoc -> HsType
tuple_tycon n = hsTyCon . tuple_tycon_name n :: SrcLoc -> HsType

hsTyTuple p ts = foldl hsTyApp (tuple_tycon (length ts-1) p) ts

isQualified = isQual :: HsName -> Bool

tupleTypeToContext t = tupleTypeToContext' is_unit_tycon_name is_tuple_tycon_name t
is_tuple_tycon_name arity n = n==tuple_tycon_name arity undefined
is_unit_tycon_name n = n==unit_tycon_name undefined

-- An omitted module header is equivalent to module Main(main) where ...
hsMainModule loc body =
    hsModule loc (pos (main_mod (srcFile loc)) loc)
             (Just [exportVar (main_name loc)]) body
main_name = pos Hs.main_name
