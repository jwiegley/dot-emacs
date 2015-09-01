module Let where

import PointlessP.Functors

{- imports will be added for the PointlessP librasies -}

-- the whole expression will be selected for translation.
isort =
   let leq = \x y -> if (==0) x then True
                          else if y==0 then False
                               else leq (pred x) (pred y)

   in let insert = \x lst ->
                     if null lst then [x]
                     else if (leq x (head lst))
                          then x : lst
                          else (head lst) : (insert x (tail lst))

      in let isort = \lst -> if (null lst)
                             then []
                             else insert (head lst) (isort (tail lst))

         in isort


