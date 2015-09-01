module MonadIn1 where

f :: Monad m => m Int
f = do 
       let x@(y:ys) = [1,2]
       return y


