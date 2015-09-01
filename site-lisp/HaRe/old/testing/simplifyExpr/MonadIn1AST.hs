module MonadIn1 where
f :: Monad m => m Int
 
f   =   do let x@((y : ys)) = [1, 2]
           case x of
               (z : zs) -> return z
 
f_1 =   do let x@((y : ys)) = [1, 2]
           case x of
               (z : zs) -> return 0
 