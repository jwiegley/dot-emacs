module Renaming.QualServer
  (
  foo
  ) where

{- foo is imported qualified as in QualClient. Renaming should
   preserve the qualification there
-}


foo :: Char
foo = 'a'
