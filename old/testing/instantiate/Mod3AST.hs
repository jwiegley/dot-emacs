module Mod3 where
f1 0 l = take 42 l
f1 n l = take n l
 
f2 0 "hi" = drop 0 "hi"
f2 0 l = drop 0 l
f2 n l = drop n l
 
g = 42
 