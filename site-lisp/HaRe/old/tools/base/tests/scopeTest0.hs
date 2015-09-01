module ScopeTest0 where

id x = x

skk = id

bla = blaha

not True = False
not False = True

f = \ x -> \ x -> x
  where
    g = \ x -> x
    x = True
