{-# OPTIONS_GHC -cpp  #-}
{-+
This module implements environments (symbol tables) as finite maps.
Finite maps are not necessarily faster than simple association lists, since
although lookups change from O(n) to O(log n), extension changes from
O(1) to O(log n), and the latter cost can be the dominating cost...
-}
module TiEnvFM(Env,extenv1,extenv,empty,lookup,domain,range) where
import Prelude hiding (lookup) -- for Hugs
import qualified Prelude -- Haskell report change workaround

import Map60204
--import PrettyPrint(Printable(..),fsep) -- for debugging

#if __GLASGOW_HASKELL__ >= 604 
import qualified Data.Map as M (Map)
newtype Env key info = Env (M.Map key info)
#else
import qualified Data.FiniteMap as M (FiniteMap)
newtype Env key info = Env (M.FiniteMap key info)
#endif  

extenv1 x t (Env bs) = Env (insertM x t bs)
extenv bs1 (Env bs2) = Env (addListToM bs2 bs1)
empty = Env emptyM

lookup (Env env) x = lookupM x env
domain (Env env) = keysM env
range (Env env) = elemsM env


-- Why isn't there a Show instance for FiniteMap?!
instance (Show key,Show info) => Show (Env key info) where
  showsPrec n (Env env) = showsPrec n (toListM env)

-- Why isn't there a Functor instance for FiniteMap?!
instance Functor (Env key) where
  fmap f (Env bs) = Env (mapM' f bs)



{-
-- For debugging:
instance (Printable key,Printable info) => Printable (Env key info) where
  ppi (Env env) = fsep (keysFM env)
-}

