module Overload where
import Maybe(isJust)

class ToBool a where toBool :: a -> Bool

instance ToBool (Maybe a) where toBool = maybeToBool

maybeToBool = isJust


assert Trivial = {True} === {True}

assert Simple = {maybeToBool (Just 'a')} === {True}

assert Overloaded = {toBool (Just 'a')} === {True}
