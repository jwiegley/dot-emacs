{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module IxStateM (HasState(..), StateM, withSt, withStS, mapState) where

import MT
import Control_Monad_Fix


newtype StateM s a   = S { ($$) :: s -> (a,s) }


withSt :: s -> StateM s a -> a
withSt s m      = fst (m $$ s)

withStS :: s -> StateM s a -> (a,s)
withStS s m     = m $$ s

mapState :: (t -> s) -> (s -> t) -> StateM s a -> StateM t a 
mapState inF outF m = S (\s -> let (a,s1) = m $$ inF s in (a, outF s1))

instance Functor (StateM s) where
    fmap f m        = m >>= return . f

instance Monad (StateM s) where
    return x  = S (\s -> (x,s) )
    f >>= g   = S (\s -> let (x,s1) = f $$ s in g x $$ s1)

instance HasState (StateM s) Z s where
    updSt  _ f = S (\s -> (s , f s))
    updSt_ _ f = S (\s -> ((), f s))
    getSt  _   = S (\s -> (s , s  ))
    setSt  _ s = S (\t -> (t , s  ))
    setSt_ _ s = S (\_ -> ((), s  ))


instance MonadFix (StateM s) where
    mfix f = S (\s -> let S m    = f a
                          (a,s1) = case m s of (a,s1) -> (a,s1)
                      in (a,s1))

instance HasBaseMonad (StateM s) (StateM s) where
  inBase = id

