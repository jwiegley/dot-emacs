module EitherIn1 where
f :: (Either a a) -> a
 
f x@(Left b_1)
    =   (case (id, id, x) of
             (f, g, (Left x)) -> f x
             (f, g, (Right y)) -> g y)
f x@(Right b_1) = either id id x
f x = either id id x
 
f_1 x@(Left b_1)
    =   (case (id, id, x) of
             (f, g, (Left x)) -> return 0
             (f, g, (Right y)) -> return 1)
 
p x@((y : ys))
    =   case x of
            [] -> 42
            (z : zs) -> zs
 