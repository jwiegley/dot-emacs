module Where1 where

data T = C1 Int Int | C2 Int

f x = g x
        where
          g x = h x
            where
              h (C1 c p) = c * p

