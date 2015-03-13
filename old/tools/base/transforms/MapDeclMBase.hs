module MapDeclMBase (module MapDeclM) where

import MapDeclM
import MapDeclMBaseStruct() -- get the instances
import Syntax

instance MapDeclM (HsDeclI i) [HsDeclI i] where
    mapDeclM = std_mapDeclM

instance MapDeclM (HsExpI i) [HsDeclI i] where
    mapDeclM = std_mapDeclM




