{-+
The Stratego syntax for terms is what one gets with derived Show
instances in Haskell, except for constructors with exactly one argument,
which have to be wrapped in parentheses. We use the type P below to
get explicit parentheses from the derived Show instances.

(We use tuples for constructors with more than one argument, so they
will be printed as expected by Stratego, but there are no tuples of
arity 1 in Haskell...)
-}
module Parentheses where

newtype P a = P a deriving (Eq,Ord)

instance Show a => Show (P a) where
  showsPrec n (P x) = showString "(" . shows x . showString ")"

{- -- not needed at the moment...
instance Read a => Read (P a) where
  readsPrec n s = [(P x,r)| ("(",r0)<-lex s,
			    (x,r1)<-reads r0,
			    (")",r)<-lex r1]
-}
