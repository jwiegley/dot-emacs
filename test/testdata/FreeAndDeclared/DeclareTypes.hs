{-# LANGUAGE TypeFamilies #-}
module FreeAndDeclared.DeclareTypes  where

-- Type families

-- See http://www.haskell.org/haskellwiki/GHC/Type_families
-- Declare a list-like data family
data family XList a

-- Declare a list-like instance for Char
data instance XList Char = XCons !Char !(XList Char) | XNil

-- Declare a number-like instance for ()
data instance XList () = XListUnit !Int

-- -------------------------------------


data X = Y Integer | Z | W Foo

type Foo = Integer

class Bar a where
  type BarVar a
  data BarData a :: * -> *

  doBar :: a -> Int





