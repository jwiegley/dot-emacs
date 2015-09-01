module TokenTags where
import Data.Ix

data TokenTag
  = Comment | Reserved | Var | Con | TCon | VarOp | ConOp | Lit | ModName
  deriving (Eq,Ord,Ix,Bounded,Show)
