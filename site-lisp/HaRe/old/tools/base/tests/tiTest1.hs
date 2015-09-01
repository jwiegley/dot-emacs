module Test1 where

class C a where
  op :: a -> Bool

instance C [a] where op _ = True

{-
f xs = (let g :: a->Bool
            g y = op (xs>>return y)
        in True,
        xs++[])
--}
--{-
g xs = (xs++[],
        let g :: a->Bool
            g y = op (xs>>return y)
        in True)
--}
