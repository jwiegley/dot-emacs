module EnvMT (module IxEnvMT, F.MT(..), F.HasEnv, getEnv, inEnv, inModEnv) where

import IxEnvMT hiding (HasEnv(..))
import qualified MT as F 

getEnv    :: F.HasEnv m F.Z e => m e
inEnv     :: F.HasEnv m F.Z e => e -> m a -> m a
inModEnv  :: F.HasEnv m F.Z e => (e -> e) -> m a -> m a

getEnv    = F.getEnv F.this 
inEnv     = F.inEnv F.this 
inModEnv  = F.inModEnv F.this 





