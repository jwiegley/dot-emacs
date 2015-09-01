module Runnable where


class Runnable0 m where
    runM0 :: m a -> a

class Runnable1 m h where
    runM1  :: h -> m a -> a
    runM1' :: h -> m a -> (a,h)

    runM1  h m = fst (runM1' h m)
    runM1' h m = (runM1 h m, h)

class Runnable2 m f where
    runM2 :: f a -> m a -> a

class Monad m => Runnable m a | m -> a where
    runM :: a -> m b -> b
