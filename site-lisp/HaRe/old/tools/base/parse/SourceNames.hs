module SourceNames where
import UniqueNames
import HsName

instance Unique HsName      where unique m n = G m (hsUnQual n) noSrcLoc
instance Unique Id          where unique m n = G m n noSrcLoc

srcName (PN n _) = n
