-- Dummy Dynamic module
module Dynamic where

data Dynamic
data TypeRep
data TyCon

instance Show Dynamic

class Typeable a where
  typeOf :: a -> TypeRep

fromDyn :: (Typeable a) => Dynamic -> a -> a
fromDyn = undefined

toDyn :: (Typeable a) => a -> Dynamic
toDyn = undefined

mkTyCon :: String -> TyCon
mkTyCon = undefined

mkAppTy :: TyCon   -> [TypeRep] -> TypeRep
mkAppTy = undefined

instance Typeable Int where
    typeOf = undefined
