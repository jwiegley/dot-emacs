{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Recursive where

{-+
This module defines a general class for converting to/from a recursive type
and its underlying structure.
-}

class Rec r struct | r -> struct where
  r    :: struct -> r
  struct :: r    -> struct

  mapRec :: (struct ->struct) -> r -> r
  mapRec f = r . f . struct
