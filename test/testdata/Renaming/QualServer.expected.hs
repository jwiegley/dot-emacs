module Renaming.QualServer
  (
  foo1
  ) where

{- foo is imported qualified as in QualClient. Renaming should
   preserve the qualification there
-}


foo1 :: Char
foo1 = 'a'
