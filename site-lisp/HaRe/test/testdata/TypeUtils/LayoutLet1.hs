module LayoutLet1 where

-- Simple let expression, rename xxx to something longer or shorter
-- and the let/in layout should adjust accordingly

foo xxx = let a = 1
              b = 2
          in xxx + a + b

