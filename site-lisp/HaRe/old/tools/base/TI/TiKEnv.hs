module TiKEnv(KEnv,extenv1,extenv,empty,lookup,domain,range) where
import Prelude hiding (lookup)
import TiEnvFM
import HsIdent(HsIdentI)
import TiTypes(Kind,TypeInfo)

type KEnv i = Env (HsIdentI i) (Kind,TypeInfo i) -- kind of type identifiers
