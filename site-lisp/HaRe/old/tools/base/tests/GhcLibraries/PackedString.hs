module PackedString where
import qualified Prelude as P
import Prelude hiding (null)

newtype PackedString = PS String deriving (Eq,Ord)

instance Show PackedString where
  showsPrec n (PS s) r = s++r

packString = PS
unpackPS (PS s) = s

null (PS s) = P.null s

