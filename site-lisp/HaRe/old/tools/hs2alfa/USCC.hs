module USCC(decls) where
import UFree
import UAbstract(Decls,Def,defaNames,Var(..),decl')
import TiSCC
import FreeNames
import DefinedNames
import HsIdent(HsIdentI(..))

decls = map decl' . sccD :: [Def] -> Decls

instance FreeNames Var Def where
  freeNames = map (flip (,) ValueNames . HsVar) . free

instance DefinedNames Var Def where
  definedNames = map (flip (,) Value . HsVar) . defaNames
