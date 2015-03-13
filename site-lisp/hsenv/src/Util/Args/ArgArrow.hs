{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Util.Args.ArgArrow ( ArgArrow
                          , runArgArrow
                          , liftIO
                          , addKnownArg
                          , askArgs
                          , getKnownArgs
                          ) where

import Util.StaticArrowT (StaticArrowT(..), addStatic, getStatic)
import Util.Args.RawArgs (Args)
import Util.Args.ArgDescr (KnownArgs)
import Data.Monoid (mempty)
import Control.Monad.Reader (ReaderT(..), ask)
import qualified Control.Monad.Reader as Reader (liftIO)
import Control.Arrow (Kleisli(..), Arrow, ArrowChoice)
import Control.Category (Category)

-- cli options parsing arrow, that exports statically all known args, and their info
newtype ArgArrow a b = ArgArrow (StaticArrowT KnownArgs (Kleisli (ReaderT Args IO)) a b)
    deriving (Category, Arrow, ArrowChoice)

runArgArrow :: ArgArrow () a -> Args -> IO a
runArgArrow (ArgArrow (StaticArrowT _ m)) = runReaderT $ runKleisli m ()

liftIO :: (a -> IO b) -> ArgArrow a b
liftIO m = ArgArrow $ StaticArrowT mempty $ Kleisli (Reader.liftIO . m)

-- record statically new known argument
addKnownArg :: KnownArgs -> ArgArrow () ()
addKnownArg = ArgArrow . addStatic

-- returns raw parsed args
askArgs :: ArgArrow () Args
askArgs = ArgArrow $ StaticArrowT mempty $ Kleisli $ const ask

-- returns statically known (by this computation) cli args
getKnownArgs :: ArgArrow a b -> KnownArgs
getKnownArgs (ArgArrow arrow) = getStatic arrow
