
module RenameParamIn6 where

{- de xs = deleteBy (==) 0 xs -}

de xs = (let y = head xs
              
             ys = tail xs
         in if xs == []
            then []
            else if (==) 0 y
                 then ys
                 else y : (de ys))

deleteBy eq x list = if list == [] then []
                                   else if eq x y then ys else y : deleteBy eq x ys
                                    where
                                      y = head list
                                      ys = tail list


