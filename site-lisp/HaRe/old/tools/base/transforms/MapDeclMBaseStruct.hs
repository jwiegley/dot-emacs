module MapDeclMBaseStruct where

import MapDeclM(MapDeclM,mapDeclM)
import HsDecl
import HsExp
import HsModule(HsModuleI)
import HsModuleMaps(seqDecls,mapDecls)

-- we assume only "expressions" & "declarations" may contain declarations
instance MapDeclM e ds => MapDeclM (DI i e p ds t c tp) ds where
    mapDeclM f = seqDI . mapDI return (mapDeclM f) return f return return return

instance MapDeclM e ds => MapDeclM (EI i e p ds t c) ds where
    mapDeclM f = seqEI . mapEI return (mapDeclM f) return f return return

instance MapDeclM (HsModuleI m i ds) ds where
    mapDeclM f = seqDecls . mapDecls f
