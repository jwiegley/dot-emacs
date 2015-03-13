{-# LANGUAGE TemplateHaskell #-}
{-# LANGUGE QuasiQuotes #-}

{- Main.hs -}
module TH.Main where

-- Import our template "pr"
import TH.Printf

-- The splice operator $ takes the Haskell source code
-- generated at compile time by "pr" and splices it into
-- the argument of "putStrLn".
main = putStrLn ( $(pr "Hello") )

-- import Control.Lens
-- data Foo a = Foo { _fooArgs :: [String], _fooValue :: a }
-- makeLenses ''Foo

-- main = putStrLn "hello"

-- longString = [str| hello |]


baz = 'a'

sillyString = [e|baz|]

