module Where1 where
data T = C2 Int
 
f x = g x
  where
      g x = error "h x no longer defined for T at line: 3"
 