{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

{-

Inspired by http://brianmckenna.org/blog/type_annotation_cofree
and its gist at https://gist.github.com/puffnfresh/5940556

-}

module CoFreeGhc where

import Prelude hiding (sequence)

import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.State hiding (sequence)
import Data.Foldable (Foldable) -- , fold)
-- import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Traversable (Traversable, sequence)
import qualified Data.Map as M

-- But for now we want a normal recursive AST. If we use a fixed-point we
-- can get a normal one using `Mu AST`.

newtype Mu f = Mu (f (Mu f))

{-
We need to convert our example AST from `Mu` into `Cofree`. Cofree
takes a parameterised type and makes it recursive with each step
having an attribute. Our initial attribution will be unit (i.e. we'll
initially use Cofree just for the recursive comonadic structure).
-}

cofreeMu :: Functor f => Mu f -> Cofree f ()
cofreeMu (Mu f) = () :< fmap cofreeMu f

-- from "Generic programming with fixed points for mutually recursive
--       datatypes"

data Fix f =In {out :: (f (Fix f))}

data Expr      = Const Int | Add Expr Expr | Mul Expr Expr

data PFExpr r = ConstF Int | AddF r r      | MulF r r

type Expr' = Fix PFExpr

class Regular a where
  deepFrom :: a -> Fix (PF a)
  deepTo   ::      Fix (PF a) -> a

  from :: a -> PF a a
  to   ::      PF a a -> a

type family PF a :: * -> *

type instance PF Expr = PFExpr


instance Functor PFExpr where
  fmap f (ConstF i) =ConstF i
  fmap f (AddF e e')=AddF (f e) (f e')
  fmap f (MulF e e')=MulF (f e) (f e')



