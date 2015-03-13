module IfThenElseIn1 where

-- refactorer should give an error!

f x@(y:ys) = if x == [] then error "Error!"
                        else y



