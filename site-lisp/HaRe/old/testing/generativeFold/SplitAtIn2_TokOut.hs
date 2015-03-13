module SplitAt2 where


{- splitIt n xs = splitAt (n - 1) xs -}

splitIt n xs = case (n-1, xs) of
                (0, xs) -> ("", xs)
                (_, "") -> ("","")
                (m, (x:xs)) -> (x:xs', xs'')
                   where (xs', xs'') = splitIt (n - 1) xs

{- this time the where is bound to the case alternative
   and thus m is in scope... -}








{- splitIt 0 xs	   = ("", xs)
splitIt _  xs@("")  = (xs, xs)
splitIt m (x:xs) = (x:xs', xs'')
  where
   (xs', xs'') = splitAt (m - 1) xs -}