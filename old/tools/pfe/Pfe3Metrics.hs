module Pfe3Metrics where
import Data.Maybe(mapMaybe)

import PFE0(allModules,pput)
import PFE3(parseModule)
import HsDeclStruct(DI(..))
import HsModule(hsModDecls)
import DefinedNames(definedType)
import HasBaseStruct(basestruct)
import Statistics

import PfeParse
import MUtils

pfe3MetricsCmds =
  [("classmetrics", (noArgs classMetrics,"number of instances per class metrics"))]
classMetrics =
  do ms <- allModules
     (classes,insts) <- apBoth concat . unzip # mapM getClassInstDecls ms
     let cinstcnt = [(c,length [()|i<-insts,i==c])|c<-classes]
     pput (ppStatistics "number of instances" "class" cinstcnt)

getClassInstDecls m = cls_insts . hsModDecls . snd # parseModule m

cls_insts ds = (mapMaybe className ds,concatMap instClass ds)

className d =
  case basestruct d of
    Just (HsClassDecl _ _ tp _ _) -> Just (definedType tp)
    _ -> Nothing

instClass d =
  case basestruct d of
    Just (HsInstDecl _ _ _ tp _) -> [definedType tp]
    Just (HsDataDecl _ _ _ _ cls) -> cls
    Just (HsNewTypeDecl _ _ _ _ cls) -> cls
    _ -> []
