{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TypeFamilies #-}
 module TypeUtils.TyClDEcls where


-- Declare a list-like data family
data family XList a

-- Declare a list-like instance for Char
data instance XList Char = XCons !Char !(XList Char) | XNil

data Foo = Foo Int

type Foo2 = String

class Bar a where
  bar :: a -> Bool

