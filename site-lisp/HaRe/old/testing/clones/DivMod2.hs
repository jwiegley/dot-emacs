module DivMod2 where


f x y = x `p` y
         where
           p = (+)           

g y h = h (-) y
         where
           q = (-)