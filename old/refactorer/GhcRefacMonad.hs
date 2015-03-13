module GhcRefacMonad (Refact, ParseResult, RefactState(RefSt), runRefact) where

import Control.Monad.State


import qualified Bag           as GHC
import qualified BasicTypes    as GHC
import qualified DynFlags      as GHC
import qualified FastString    as GHC
import qualified GHC           as GHC
import qualified GHC.Paths     as GHC
import qualified HsSyn         as GHC
import qualified Module        as GHC
import qualified MonadUtils    as GHC
import qualified Outputable    as GHC
import qualified RdrName       as GHC
import qualified SrcLoc        as GHC
import qualified TcEvidence    as GHC
import qualified TcType        as GHC
import qualified TypeRep       as GHC
import qualified Var           as GHC
import qualified Coercion      as GHC
import qualified ForeignCall   as GHC
import qualified InstEnv       as GHC
import SrcLoc1
import TermRep
import Unlit
import GhcRefacTypeSyn


data RefactState = RefSt
	{ rsTokenStream :: [PosToken]
	, rsStreamAvailable :: Bool
	, rsPosition :: (Int,Int)
	}

type ParseResult inscope = ([inscope], [GHC.LIE GHC.RdrName], GHC.ParsedSource)

newtype Refact a = Refact (StateT RefactState IO a)
instance MonadIO Refact where
	liftIO f = Refact (lift f)

runRefact :: Refact a -> RefactState -> IO (a, RefactState)
runRefact (Refact (StateT f)) s = f s


instance Monad Refact where
  x >>= y = Refact (StateT (\ st -> do (b, rs') <- runRefact x st
				       runRefact (y b) rs'))

  return thing = Refact (StateT (\ st -> return (thing, st)))


instance MonadPlus Refact where
   mzero = Refact (StateT(\ st -> mzero))

   x `mplus` y =  Refact (StateT ( \ st -> runRefact x st `mplus` runRefact y st))  -- Try one of the refactorings, x or y, with the same state plugged in


instance MonadState RefactState (Refact) where
   get = Refact $ StateT ( \ st -> return (st, st))

   put newState = Refact $ StateT ( \ _ -> return ((), newState))
