-- Environemnts (symbol tables)
module TiEnv(Env,extenv1,extenv,empty,lookup,domain,range) where
import Prelude hiding (lookup) -- for Hugs
import qualified Prelude -- Haskell report change workaround

-- Simplest possible implementation...
newtype Env key info = Env [(key,info)] deriving (Show)
-- I've tried using a FiniteMap instead, but it is slower! /TH 2002-12-05

extenv1 x t (Env bs) = Env ((x,t):bs)
extenv bs1 (Env bs2) = Env (bs1++bs2)
empty = Env []

lookup (Env env) x = Prelude.lookup x env
domain (Env env) = map fst env
range (Env env) = map snd env

instance Functor (Env key) where
  fmap f (Env bs) = Env [(k,f i)|(k,i)<-bs]
