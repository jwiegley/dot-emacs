module Monadic(module Monadic, module Monad) where

import Control.Monad

infixl 1 #, <#

( # )         :: Monad m => (a -> b) -> (m a -> m b)
( # )         = liftM

(<#)          :: Monad m => m (a -> b) -> m a -> m b
(<#)          = ap


whenM         :: Monad m => m Bool -> m () -> m ()
whenM p m     = do b <- p; when b m

unlessM       :: Monad m => m Bool -> m () -> m ()
unlessM p m   = whenM (notM p) m

notM          :: Monad m => m Bool -> m Bool
notM p        = liftM not p

whileM        :: Monad m => m Bool -> m () -> m ()
whileM p m    = whenM p (m >> whileM p m)

untilM        :: Monad m => m () -> m Bool -> m ()
m `untilM` p  = m >> unlessM p (m `untilM` p)


m <&& n       = do b <- m 
                   if b then n else return False
m <|| n       = do b <- m
                   if b then return True else n
  
allM p xs     = foldr (<&&) (return True) (map p xs)
anyM p xs     = foldr (<||) (return False) (map p xs)





