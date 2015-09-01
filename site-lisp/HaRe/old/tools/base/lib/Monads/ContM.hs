module ContM (HasCont(..), runCont, ContM) where

import MT


import Control.Monad


newtype ContM o i = C { ($$) :: (i -> o) -> o }

runCont :: ContM i i -> i
runCont m       = m $$ id


instance Monad (ContM o) where
  return x    = C (\k -> k x)
  C m >>= f   = C (\k -> m (\i -> f i $$ k))
  C m >> C n  = C (m . const . n)

instance HasBaseMonad (ContM o) (ContM o) where
  inBase        = id


instance HasCont (ContM o) where
  callcc f    = C (\k -> f (\a -> C (\d -> k a)) $$ k)



shift           :: ((a -> ContM b b) -> ContM b b) -> ContM b a
shift f         = C (\k -> runCont $ f (\a -> C (\k' -> k' (k a))))

reset           :: ContM a a -> ContM a a
reset m         = return (runCont m)


{-
test1           = do x <- reset $ do y <- shift (\f -> do z <- f "100"
                                                          f z)
                                     return ("10 + " ++ y)
                     return $ "1 + " ++ x


test2           = liftM ("1 + " ++) $ reset $ liftM ("10 + " ++) $ shift (\f -> return "100")
test3           = liftM ("1 + " ++) $ reset $ liftM ("10 + " ++)  $ shift $ \f -> liftM2 (\x y -> x ++ " + " ++ y) (f "100") (f "1000")
-}

