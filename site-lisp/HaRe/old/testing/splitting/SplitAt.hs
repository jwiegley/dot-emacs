module SplitAt where

import Prelude hiding ( splitAt)

splitAt :: Int -> String -> (String, String)
splitAt 0 xs = ("", xs)
splitAt _ "" = ("", "")
splitAt n (x:xs)
 | n > 0 = (x:ys, zs) 
   where
    (ys, zs) = splitAt (n-1) xs
splitAt _ _ = (error "PreludeList.take: negative argument",
               error "PreludeList.drop: negative argument")


