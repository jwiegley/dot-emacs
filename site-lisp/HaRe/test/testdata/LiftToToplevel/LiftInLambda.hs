module LiftToToplevel.LiftInLambda where

foo :: IO ()
foo = do
  let
    xx = map (\b -> (b,uses declaredPns [b])) []
  return ()

  where
    uses pns t2 = concat $ everythingStaged  (++) []

    declaredPns = undefined
    everythingStaged = undefined

