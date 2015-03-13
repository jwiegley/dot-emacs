module Visible.Simple where

-- Both a and b should be visible in the RHS
params :: Int -> Int -> Int
params a b = a + b

-- B should be free, x declared, from RHS
param2 :: B -> Int
param2 (B x) = x



data B = B Int
