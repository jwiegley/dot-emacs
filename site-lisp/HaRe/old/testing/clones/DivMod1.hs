
module DivMod1 where



emitJump p j i = emitByte p (show l) (show h) 
            where
               (h,l) = divMod i 256

emitOp12 p op i =
    if i < 0 then
     case divMod (-i) 256 of
       (0,l) -> emitByte p "null op" "null op"
       (x,y) -> dummy p (show x) (show y)
     else
      case divMod i 256 of
        (0,l) -> emitByte p "null p1" "null op"
        (n,m) -> emitByte p (show n) (show m)

emitByte p x y = x ++ y

dummy x y z = y + z

o x y z w = (emitByte, x + y + z + w)

k = (emitByte, 1 + 2 + 3 + 4)
