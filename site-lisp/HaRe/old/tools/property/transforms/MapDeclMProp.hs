module MapDeclMProp where
import MapDeclM
import PropSyntax
import MapDeclMPropStruct() -- get the instances
import MapDeclMBaseStruct() -- get the instances

instance MapDeclM (HsDeclI i)    [HsDeclI i] where mapDeclM = std_mapDeclM
instance MapDeclM (HsExpI i)     [HsDeclI i] where mapDeclM = std_mapDeclM
instance MapDeclM (AssertionI i) [HsDeclI i] where mapDeclM = std_mapDeclM
instance MapDeclM (PredicateI i) [HsDeclI i] where mapDeclM = std_mapDeclM

