module TiFreeNames(module TiFreeNames,FreeNames(..)) where
import FreeNames
import HsIdent
import Data.Maybe(mapMaybe)

freeTypeNames x = mapMaybe freeTypeName . freeNames $ x
freeValueNames x = mapMaybe freeValueName . freeNames $ x

freeVars x = filter isHsVar . freeValueNames $ x
freeTyvars x = filter isHsVar . freeTypeNames $ x

freeTypeName (n,ClassOrTypeNames) = Just n
freeTypeName (n,_) = Nothing

freeValueName (n,ValueNames) = Just n
freeValueName (n,_) = Nothing

-- Get the type parameters from the lhs of a type/newtype/data/class decl:
typeParams tp = [v|HsVar v<-freeTyvars tp] -- Hmm. Order?
