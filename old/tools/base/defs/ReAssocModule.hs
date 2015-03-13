module ReAssocModule where
import ReAssoc(reAssoc')
import WorkModule
import QualNames
import Ents
import TypedIds(namespace,NameSpace(..))

import Lift
import MUtils

reAssocModule wm origOps mod = reAssoc' opEnv mod
  where
    opEnv = [(q,fixity)|qn<-inScopeDom wm,
			Ent m n t <-inScope wm qn,
			namespace t==ValueNames,
			--m/=mn, -- only imported names
			let --un = mapHsIdent UnQual n
			    q = requal qn n,
			fixity<-lift (lookupOrig m n origOps)]

    lookupOrig m n = lookup n @@ lookup m

    requal qn n = case getQualifier qn of
                    Nothing -> mkUnqual n
                    Just m  -> mkQual m n

