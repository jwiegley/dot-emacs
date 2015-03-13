module Deriving where
import DerivingEq
import DerivingShow
import DerivingBounded
import DerivingEnum
import DerivingOrd
import DerivingRead
import DerivingIx
import DerivingUtils
import PrettyPrint
import Lift(lift)
import SrcLoc1(srcLoc)

derive stdnames cl t =
    case lookup cl derivers of
      Nothing -> fail $ pp $"Don't know how to derive"<+>cl
      Just d -> d stdnames' (srcLoc cl) =<< tinfo
  where
    stdnames' m n = lift (stdnames m n)
    tinfo =
      case idTy t of
	Type tinfo@TypeInfo{defType=Just tkind}
           | tkind `elem` [Data,Newtype] -> return (idName t,tinfo)
	_ -> fail $ pp $ "Deriving"<+>cl<>": this is not a data/newtype:"<+>t
{-
    conv tinfo@(TypeInfo d cs fs) = TypeInfo d (map convc cs) [] -- !!fields
      where
        convc (ConInfo c n optfs) =
          ConInfo (PNT (mkUnqual c) ConstrOf{} noSrcLoc)
		  n
		  Nothing -- !! field names are discarded
-}
    derivers =
	concat
	[pc "Eq"  deriveEq,
	 pc "Show" deriveShow,
	 pc "Bounded" deriveBounded,
	 pc "Enum" deriveEnum,
	 pc "Ord" deriveOrd,
	 pc "Read" deriveRead,
	 ixc "Ix" deriveIx]

    pc = stdc mod_Prelude
    ixc = stdc mod_Ix
    stdc m n d = either ignore keep (stdclass stdnames m n)
      where
        keep (HsCon c) = [(c,d)]
	ignore _ = []
