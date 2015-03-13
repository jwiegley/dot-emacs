{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
module ScopeNames where
import EnvM
import DefinedNames(TypedIdent)
import MUtils
import Recursive

type Env i = [TypedIdent i]

class ScopeNames i e s1 s2 | s1->i, s1 e->s2  where
  scopeNames :: (Env i->e->e)->s1->EnvM e s2

instance ScopeNames i e s1 s2 => ScopeNames i e [s1] [s2] where
  scopeNames = mapM . scopeNames

instance ScopeNames i e s1 s2 => ScopeNames i e (Maybe s1) (Maybe s2) where
  scopeNames ext = seqMaybe . fmap (scopeNames ext)

instance (ScopeNames i e a1 a2,ScopeNames i e b1 b2)
      => ScopeNames i e (a1,b1) (a2,b2) where
  scopeNames ext (a,b) = (,) # scopeNames ext a <# scopeNames ext b


scopeNamesRec ext s = r # scopeNames ext (struct s)

{-
class ScopeNames i s | s->i where
  envNames :: s -> ScopeM i s

penv x = (,) x # getEnv

--cpenv = penv . HsCon
--vpenv = penv . HsVar

scopeNames f env0 = runEnv [] . seqNames . flip envNames env0 . mapNames f

extend env1 m = \ env2 -> m (env1++env2)
-}
