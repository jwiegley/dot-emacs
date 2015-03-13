module TiSuper where

-- Testing the use of the superclass relation in context reduction

f :: Real a => a -> a -> (a,Bool)
f x y = (x+y,x>y)
{-
convert :: Integral a => a->a
convert x = fromInteger (toInteger x)

--showSigned    :: Real a => (a -> ShowS) -> Int -> a -> ShowS
showSigned showPos p x | x < 0 = showParen ((p::Int) > 6)
                                           (showChar '-' . showPos (-x))
                       | otherwise = showPos x

primitive showParen :: Bool -> ShowS -> ShowS
type ShowS = String->String
primitive showChar :: Char->ShowS
-}
