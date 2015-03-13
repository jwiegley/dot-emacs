-- $Id: Compile.hs,v 1.2 2001/09/20 21:34:13 hallgren Exp $

module Compile where

import Monad(liftM)

data Compile a = Good a | CompileError String


instance Functor Compile where fmap = liftM

instance Monad Compile where
    return = Good
    m >>= f = case m of
              Good s           -> f s
              CompileError err -> CompileError err

compileError = CompileError
