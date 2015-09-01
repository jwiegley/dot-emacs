module SubstituteBaseStruct where
import Substitute
import Recursive
import HasBaseStruct
import BaseSyntax

substE = substE' r

substE' r s e0 =
    case mapEI id (subst s) id (esubst s) id id e0 of
      HsId (HsVar x) -> s x
      HsInfixApp e1 (HsVar x) e2 -> s x `hsApp` e1 `hsApp` e2
      HsLeftSection e (HsVar x) -> s x `hsApp` e
      HsRightSection (HsVar x) e -> error "SubstituteBaseStruct.subst HsRightSection"
      e -> r e

instance MapExp e ds => MapExp e (DI i e p ds t c tp) where mapExp = mapExpD
instance MapExp e ds => MapExp e (EI i e p ds t c)    where mapExp = mapExpE

mapExpD f = mapDI id f id (mapExp f) id id id
mapExpE f = mapEI id f id (mapExp f) id id

instance MapExp e ds => MapExp e (HsMatchI i e p ds) where
  mapExp f = mapMatchI id f id (mapExp f)

instance MapExp e ds => MapExp e (HsModuleI m i ds) where
  mapExp = mapDecls . mapExp


