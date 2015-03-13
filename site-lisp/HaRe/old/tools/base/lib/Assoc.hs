module Assoc where

import OpTypes
import Data.List(partition)
import Data.Maybe (listToMaybe)
import Products
import EnvM


class (Prod2 p k v, Functor c) => AssocC c p k v where

    -- define:
    lkpAllEq        :: EqOp k -> k -> EnvM (c p) [v]
    splitAssoc      :: (k -> Bool) -> EnvM (c p) (c p, c p)

{-
    lkpDefEq        :: EqOp k -> v -> k -> EnvM (c p) v
    nonfailLkpEq    :: EqOp k -> k -> EnvM (c p) v

    lkp             :: Eq k => k -> EnvM (c p) (Maybe v)
    lkpDef          :: Eq k => v -> k -> EnvM (c p) v
    nonfailLkp      :: Eq k => k -> EnvM (c p) v

    keys            :: EnvM (c p) (c k)
-}

lkpEq eq i      = listToMaybe . lkpAllEq eq i
lkpDefEq eq v k = maybe v id . lkpEq eq k
nonfailLkpEq eq = lkpDefEq eq (error "nonfailLkp failed.")
lkpAll x        = lkpAllEq (==) x
lkp x           = lkpEq (==) x
lkpDef x        = lkpDefEq (==) x
nonfailLkp x    = nonfailLkpEq (==) x
keys x          = fmap proj1 x


instance Prod2 p k v => AssocC [] p k v where
    lkpAllEq eq i   = map proj2 . filter (eq i . proj1)
    splitAssoc p    = partition (p . proj1)


type Assoc a b      = [(a,b)]




