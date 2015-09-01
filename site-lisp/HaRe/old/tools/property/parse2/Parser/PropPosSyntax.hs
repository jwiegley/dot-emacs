module PropPosSyntax(module PropPosSyntax,module PosName,module Hs,SN) where
import PropSyntax as Hs hiding (ModuleName,HsName,Id{-,HsIdent,HsField(),HsImportDecl(),HsConDecl(),HsExportSpec,HsImportSpec-},hsTyTuple)
import qualified PropSyntax as Hs
import HsConstants as Hs(main_mod,tuple,mod_Prelude')
import qualified HsConstants as Hs
--import PrettyPrint
import SourceNames
import PosName
--import SpecialNames as Hs
import QualNames(isQual)
--import Entity()

pos i p = SN i p

type HsExp = HsExpI HsName
type HsPat = HsPatI HsName
type HsDecl = HsDeclI HsName
type HsType = HsTypeI HsName

type HsQualType = HsQualTypeI HsName
type Assertion = AssertionI HsName
type Predicate = PredicateI HsName


type HsField = Hs.HsFieldI HsName
type HsImportDecl = Hs.HsImportDeclI ModuleName HsName
type HsConDecl = Hs.HsConDeclI HsName
type HsExportSpec = Hs.HsExportSpecI ModuleName HsName
type HsImportSpec = Hs.HsImportSpecI HsName
type HsModuleR = Hs.HsModuleI ModuleName HsName [HsDecl]

qualid (p,s) = pos (splitQualName (srcFile p) s) p

unqualid (p,s) = pos (Hs.UnQual s) p

qualify m n = pos (Hs.Qual m n)

--qualified_name = pos Hs.qualified_name

{-+
The special syntax for function types, tuples and list should always refer
to the entities defined in the Prelude, even if the corresponding names are
not in scope. But the AST output from the parser can only refer to things that
are in scope, and things that have special representation in the AST.
Some type constructors currently do not have a special representation in
the AST, so to be able to refer to them we deviate from Haskell 98 by
including 'import qualified Prelude' in all modules and refering to these
entities by qualified names.
-}
unit_con_name        = qualify mod_Prelude' "()"
tuple_con_name arity = qualify mod_Prelude' $ tuple arity

unit_tycon_name = unit_con_name
list_tycon_name = qualify mod_Prelude' "[]"
fun_tycon_name = qualify mod_Prelude' "->"
tuple_tycon_name arity = tuple_con_name arity

list_tycon = Hs.hsTyCon . list_tycon_name :: Hs.SrcLoc -> HsType
tuple_tycon n = hsTyCon . tuple_tycon_name n :: SrcLoc -> HsType

qtuple n pos = qualify mod_Prelude' (tuple n) pos
qunit = qualify mod_Prelude' "()"

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
