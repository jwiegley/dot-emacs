{-# OPTIONS -cpp #-}
module Sets(module Set) where

#if __GLASGOW_HASKELL__>=604
import Data.Set as Set hiding (map,null,partition,filter,empty)
#else
import Data.Set as Set
#endif
