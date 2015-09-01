module PreludeBuiltin where

foreign import primIntToChar   :: Int -> Char
foreign import primCharToInt   :: Char -> Int
foreign import primInteger2Int :: Integer -> Int
foreign import primUnicodeMaxChar :: Char -- = '\xffff'

foreign import primIntEq       :: Int -> Int -> Bool
foreign import primIntLte      :: Int -> Int -> Bool

foreign import primIntAdd      :: Int -> Int -> Int
foreign import primIntSub      :: Int -> Int -> Int
foreign import primIntMul      :: Int -> Int -> Int
foreign import primIntQuot     :: Int -> Int -> Int
foreign import primIntRem      :: Int -> Int -> Int
foreign import primIntNegate   :: Int -> Int
foreign import primIntAbs      :: Int -> Int
foreign import primIntSignum   :: Int -> Int

foreign import primError       :: String -> a

foreign import primSeq         :: a -> b -> b

primIntQuotRem x y = (x `primIntQuot` y,x `primIntRem` y)

primCharEq c c' = primCharToInt c `primIntEq` primCharToInt c'
primCharLte c c' = primCharToInt c `primIntLte` primCharToInt c'

foreign import primInteger2Int     :: Integer -> Int
foreign import primInt2Integer     :: Int -> Integer

foreign import primIntegerLte      :: Integer -> Integer -> Bool
foreign import primIntegerEq       :: Integer -> Integer -> Bool

foreign import primIntegerAdd      :: Integer -> Integer -> Integer
foreign import primIntegerSub      :: Integer -> Integer -> Integer
foreign import primIntegerMul      :: Integer -> Integer -> Integer
foreign import primIntegerQuot     :: Integer -> Integer -> Integer
foreign import primIntegerRem      :: Integer -> Integer -> Integer
foreign import primIntegerNegate   :: Integer -> Integer
foreign import primIntegerAbs      :: Integer -> Integer
foreign import primIntegerSignum   :: Integer -> Integer
