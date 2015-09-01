module UIxStateM (HasState(..), StateM, withSt, withStS, mapState) where

import MT
import Control_Monad_Fix


newtype StateM s a   = S (s -> (# a,s #))


withSt :: s -> StateM s a -> a
withSt s (S m) = case m s of (# a,s #) -> a

withStS :: s -> StateM s a -> (a,s)
withStS s (S m) = case m s of (# a,s #) -> (a,s)

mapState :: (t -> s) -> (s -> t) -> StateM s a -> StateM t a 
mapState inF outF (S m) = S 
  (\t -> case m (inF t) of (# a,s1 #) -> (# a, outF s1 #) )

instance Functor (StateM s) where
    fmap f m        = m >>= return . f

instance Monad (StateM s) where
    return x  = S (\s -> (# x,s #) )
    S f >>= g = S (\s -> case f s of (# x,s1 #) -> 
                                       case g x of S m1 -> m1 s1)

instance HasState (StateM s) Z s where
    updSt  _ f = S (\s -> (# s , f s #))
    updSt_ _ f = S (\s -> (# (), f s #))
    getSt  _   = S (\s -> (# s , s #))
    setSt  _ s = S (\t -> (# t , s #))
    setSt_ _ s = S (\_ -> (# (), s #))


instance MonadFix (StateM s) where
    mfix f = S (\s -> let S m    = f a
                          (a,s1) = case m s of (# a,s1 #) -> (a,s1)
                      in (# a,s1 #))

instance HasBaseMonad (StateM s) (StateM s) where
  inBase = id

{- tests
foldSt :: (a -> s -> s) -> [a] -> StateM s s
foldSt f []     = getSt this
foldSt f (x:xs) = updSt_ this (f x) >> foldSt f xs
-}



