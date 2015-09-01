module RemoveIrrefPats 
  ( module RemoveIrrefPats
  , module StateM
  , module OutputMT
  , module EnvMT
  , module MT
  )where

import MT (MT(..))
import StateM
import OutputMT
import EnvMT
import SrcLoc(SrcLoc)
import HasBaseStruct(base)
import Recursive(struct)
import MUtils (( # ))

-- Monads:
-- *) the state is used as a source of new names
-- *) the environment is used for structures, that do not have a source 
--      location (e.g. expressions).  They inherit the source location 
--      of the closest enclosing them structure with a location
-- *) output is to generate pattern bindings, which delay the matching
-- *) output is also used when processing (lists of) declarations,
--    to output additional declarations generated


-- NOTE: the base monad can be generalized to be anything with state

type M i        = StateM [i]
type EM i       = WithEnv SrcLoc (M i)
type OM i ds    = WithOutput ds (M i)
type OEM i d    = WithOutput d (EM i)



-- type OEM i d    = WithOutput d (WithEnv SrcLoc (StateM [i]))


class Monad m => RemIrrefPats t m | t -> m where
    remIrrefPats :: t -> m t

-- a generic instance for lists
instance RemIrrefPats a m => RemIrrefPats [a] m where
    remIrrefPats = mapM remIrrefPats

remIrrefPatsRec p = base # remIrrefPats (struct p)

removeIrrefPats xs = withSt xs . remIrrefPats

