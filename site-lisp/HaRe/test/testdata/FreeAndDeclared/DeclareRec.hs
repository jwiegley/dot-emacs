module FreeAndDeclared.DeclareRec  where

data R = RCon { r1 :: Int, r2 :: Char }

unR (RCon a b) = a

unR2 (RCon {r1 = a}) = a





