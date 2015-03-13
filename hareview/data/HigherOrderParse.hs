{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module HigherOrderParse where

import Data.Tree

-- |Adapter class for various error types such as BNFCs ErrM etc.
-- b is the given polymorphic errortype (e.g. ErrM Program) whose 
-- parameter is a, thus we require that b -> a. Then a is the right 
-- result of Either.
class Result b a | b -> a where
  from :: b -> Either String a

instance Result (Maybe a) a where
  from (Just a) = Right a
  from Nothing  = Left "Parse error"

instance (Show b) => Result (Either b a) a where
  from (Right a) = Right a
  from (Left e ) = Left $ show e

-- |higher-order build tree
buildTreeGen :: (Result b a) 
  => (String -> b)       -- ^ some parsefunction that results in 
                         --   an instance of Result
  -> (a -> Tree String)  -- ^ some generic data2tree function
  -> String              -- ^ some input
  -> Tree String         -- ^ resulting tree
buildTreeGen parse data2tree s = 
  case (from $ parse s) of
    Right ast -> data2tree ast
    Left  err -> Node ("Parse Failed: "++err) [] 

