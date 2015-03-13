module NoEq where

{-+
If you want to derive Eq for some big datatype that contains something
that does not allow equality, you can wrap it in NoEq. For example you can
use NoEq (Int->Int) instead of (Int->Int) as an argument to a constructor.
-}

newtype NoEq a = N a

instance Eq  (NoEq a) where _ == _ = True
instance Ord (NoEq a) where compare _ _ = EQ

instance Show a => Show (NoEq a) where showsPrec n (N x) = showsPrec n x
