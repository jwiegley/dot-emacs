{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module MapDeclM where

import Recursive
import IdM

{-+
A class to apply a monadic function to all declarations in a
structure.  The type of the structure is #s#, the type of the declarations
is #d#.  The functional dependency ensures that we can determine the
type of declarations from the type of the structure.
-}

class MapDeclM s d | s -> d where
    mapDeclM :: (Functor m, Monad m) => (d -> m d) -> s -> m s

instance MapDeclM s ds => MapDeclM [s] ds where
    mapDeclM = mapM . mapDeclM

{- A convinient function, when the definition is in terms of
the underlying structure. -}

std_mapDeclM f = fmap r . mapDeclM f . struct

mapDecls f m = removeId $ mapDeclM (return.map f) m
