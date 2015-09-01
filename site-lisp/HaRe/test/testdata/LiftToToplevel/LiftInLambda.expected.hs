module LiftToToplevel.LiftInLambda where

foo :: IO ()
foo = do
  let
    xx = map (\b -> (b,(uses everythingStaged)declaredPns [b])) []
  return ()

  where

    declaredPns = undefined
    everythingStaged = undefined


uses everythingStaged pns t2= concat $ everythingStaged  (++) []

