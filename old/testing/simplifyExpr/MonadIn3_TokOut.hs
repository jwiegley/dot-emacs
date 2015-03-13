module MonadIn3 where



-- f :: (a,b,c) -> (a,b)
f (a,b,c) = 
      do
       let [z,y] = [a,b]
       return (a, b)


