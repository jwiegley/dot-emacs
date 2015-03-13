-- Dummy Int module
module Int where
import Ix

data Int8
data Int16
data Int32
data Int64

instance Eq Int8 where (==) = undefined
instance Ord Int8 where compare = undefined
instance Num Int8 where negate = undefined
instance Bounded Int8
instance Real Int8
instance Integral Int8
instance Ix Int8
instance Enum Int8
instance Read Int8
instance Show Int8 where showsPrec = undefined

instance Eq Int16 where (==) = undefined
instance Ord Int16 where compare = undefined
instance Num Int16 where negate = undefined
instance Bounded Int16
instance Real Int16
instance Integral Int16
instance Ix Int16
instance Enum Int16
instance Read Int16
instance Show Int16 where showsPrec = undefined

instance Eq Int32 where (==) = undefined
instance Ord Int32 where compare = undefined
instance Num Int32 where negate = undefined
instance Bounded Int32
instance Real Int32
instance Integral Int32
instance Ix Int32
instance Enum Int32
instance Read Int32
instance Show Int32 where showsPrec = undefined

instance Eq Int64 where (==) = undefined
instance Ord Int64 where compare = undefined
instance Num Int64 where negate = undefined
instance Bounded Int64
instance Real Int64
instance Integral Int64
instance Ix Int64
instance Enum Int64
instance Read Int64
instance Show Int64 where showsPrec = undefined
