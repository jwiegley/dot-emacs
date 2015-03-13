{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE DeriveDataTypeable  #-}

module TypedIds where
import Data.Maybe(isJust)
import Data.Generics

{-+
Haskell declaration introduce names in two name spaces. Type classes and
types live in one name space. Values (functions, data constructors) live
in another name space.
-}

data NameSpace = ClassOrTypeNames | ValueNames     deriving (Eq,Ord,Show, Data, Typeable)


{-+
Identifiers can denote many different types of entities. It is clear from
the defining occurence of an identifier what type of entity it denotes.

The type #IdTy# can be seen as a refinement of #NameSpace#.
From the use of an identifier, we can tell what name space it refers
to, but not the exact type of entity, hence the need for two different types.
-}

data IdTy i 
    = Value 
    | FieldOf i (TypeInfo i)
    | MethodOf i Int [i] -- name of class, number of superclasses, names of all methods
    | ConstrOf i (TypeInfo i)
    | Class Int [i] -- number of superclasses, names of all methods
    | Type (TypeInfo i)
    | Assertion -- P-Logic assertion name
    | Property  -- P-Logic property name
        deriving (Eq,Ord,Show,Read, Data, Typeable)
        -- These structures contain a lot of redundancy, so we shouldn't really
	-- use any comparison operations on them.

data ConInfo i = ConInfo 
    { conName :: i
    , conArity :: Int
    , conFields :: Maybe [i] -- length agrees with conArity
    } deriving (Eq,Ord,Show,Read, Data, Typeable)

data DefTy     = Newtype | Data | Synonym | Primitive
               deriving (Eq,Ord,Show,Read, Data, Typeable)

data TypeInfo i = TypeInfo
    { defType       :: Maybe DefTy
    , constructors  :: [ConInfo i]
    , fields        :: [i]
    } deriving (Eq,Ord,Show,Read, Data, Typeable)

blankTypeInfo = TypeInfo { defType = Nothing, constructors = [], fields = [] }



instance Functor ConInfo where
    fmap f c = c { conName = f (conName c),
		   conFields = fmap (map f) (conFields c) }

instance Functor TypeInfo where
    fmap f t = t { constructors = map (fmap f) (constructors t)
                 , fields = map f (fields t)
                 }

instance Functor IdTy where
    fmap f (FieldOf x tyInfo)   = FieldOf (f x) (fmap f tyInfo)
    fmap f (MethodOf x n xs)      = MethodOf (f x) n (map f xs)
    fmap f (ConstrOf t tyInfo)  = ConstrOf (f t) (fmap f tyInfo)
    fmap _ Value                = Value
    fmap f (Class n xs)         = Class n (f `map` xs)
    fmap f (Type tyInfo)        = Type (fmap f tyInfo)
    fmap _ Assertion            = Assertion
    fmap _ Property             = Property

class HasNameSpace t where
    namespace :: t -> NameSpace

instance HasNameSpace (IdTy id) where
    namespace Value         = ValueNames
    namespace (FieldOf {}) = ValueNames
    namespace (MethodOf {}) = ValueNames
    namespace (ConstrOf {}) = ValueNames
    namespace (Class {})    = ClassOrTypeNames
    namespace (Type {})     = ClassOrTypeNames
    namespace Assertion     = ValueNames -- hmm
    namespace Property      = ValueNames -- hmm


-- owner :: IdTy i -> Maybe i
owner (FieldOf dt  _) = Just dt
owner (MethodOf cl _ _) = Just cl
owner (ConstrOf dt _) = Just dt
owner _               = Nothing


-- isSubordinate :: IdTy i -> Bool
isSubordinate = isJust . owner

-- belongsTo :: idTy i -> i -> Bool
idty `belongsTo` t = owner idty == Just t

isAssertion Assertion = True
isAssertion Property  = True
isAssertion _         = False

isClassOrType,isValue :: HasNameSpace t => t -> Bool
isClassOrType   = (== ClassOrTypeNames) . namespace
isValue         = (== ValueNames)       . namespace

class HasIdTy i t | t->i where
  idTy :: t -> IdTy i

instance HasIdTy i (IdTy i) where idTy = id
--instance HasNameSpace NameSpace where namespace = id
