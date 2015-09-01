module DoIn1 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove the defintion 'k'
io  s
  = do
      let
        k = reverse s
      s <- getLine
      let
        q =(s ++ s)
      putStr q
      putStr "foo"

