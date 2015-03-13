-- $Id: InferenceMonad.hs,v 1.6 2001/03/28 22:08:56 sheard Exp $

module InferenceMonad where

import ST

data Value g b = Good g | Bad b deriving (Show, Eq)

newtype IM a e x = Ck (Int -> (ST a (Value x e, String, Int)))

instance Functor (IM a e) where
  fmap f (Ck g) = Ck h
      where h n = do { (x, out, n') <- g n
                     ; case x of 
                       Good a -> return (Good (f a), out, n')
                       Bad  w -> return (Bad w,      out, n')
                     }
                   
instance Monad (IM a t) where 
  return x = Ck h
      where h n = return (Good x, "", n)
  (Ck g) >>= f = Ck ff
      where ff n = do { (x, out1, n1) <- g n
                      ; case x of 
                        Good a -> let (Ck h) = f a
                                  in do { (y, out2, n2) <- h n1
                                        ; return (y, out1 ++ out2, n2)
                                        }
                        Bad b  -> return (Bad b, out1, n1)
                      }

---- Non standard morphisms for IM monad ----------------

----- First Mutable vars ----------------------                      
                      
readVar  :: STRef a b -> IM a c b
newRef   :: a -> IM b c (STRef b a)
writeVar :: STRef a b -> b -> IM a c ()
                       
readVar ref = Ck f 
    where f n = do { z <- readSTRef ref
                   ; return (Good z, "", n)
                   }
                 
newRef init = Ck f
    where f n = do { z <- newSTRef init
                   ; return (Good z, "", n)
                   }
                 
writeVar ref value = Ck f
    where f n = do { z <- writeSTRef ref value
                   ; return (Good z, "", n)
                   } 

nextN = Ck f
    where f n = return (Good n, "", n+1)

------------- Then printing and error handling -----------

printS s = Ck f
    where f n = return (Good (), s, n)

pr :: Show a => [Char] -> a -> IM b c ()
pr s x = printS (s ++ (show x) ++ " -\n")

raise :: a -> IM b a c
raise err = Ck f
    where f n = return (Bad err, "", n)

handle :: IM a b c -> (b -> IM a b c) -> IM a b c
handle (Ck m) f = Ck h
    where h n = do { (x, out1, n') <- m n
                   ; case x of
                     Good y -> return (x, out1, n')
                     Bad y  -> let Ck a = f y
                               in do { (b, out2, m) <- a n'
                     ; return (b, out1 ++ out2, m) 
                     }
                   }

-------------- Finally the run function for the monad --------------  

runIM :: (forall a . IM a e c) -> Int -> (Value c e,String,Int)
runIM w n = let (Ck f) = w in runST (f n)
  
  
force :: (forall a . IM a e c) -> c
force w =
    case (runIM w) 0 of
    (Good x, _, _) -> x
    (Bad x,  s, _) -> error ("error in Inference monad: " ++ s)
     

display :: Show c => (forall a . IM a e c) -> String
display a =
    case (runIM (do { x <- a ; pr "" x })) 0 of
    (_, s, _) -> s

perform :: Show a => (forall c. IM c a String) -> IO ()
perform x =
  case runIM x 0 of
    (Good x,message,n) -> do { putStrLn ("Good\n"++message); putStrLn"\n--------------\n"
                             ; putStrLn x }
    (Bad y, message,n) -> do { putStrLn ("Bad\n"++message); putStrLn"\n--------------\n"
                             ; putStrLn (show y) }