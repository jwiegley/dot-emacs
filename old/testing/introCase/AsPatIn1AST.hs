module AsPatIn1 where
f :: (Either a b) -> Either a b
 
f x@x_1
    =   case x of
            x@(Left b_1) -> x_1
            x@(Right b_1) -> x_1
f x@x_1 = x_1
 