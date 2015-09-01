{-+
Packaging some of the available source transformations as named rewrites.
-}
module PFE_Rewrites(module PFE_Rewrites,module PFE_Rewrite,module PFE_StdNames)
where
import RemovePatBinds(remPats)
import RemoveListComp(rmAllListComp)
import SimpPatMatch(simpAllPatMatch,getSimpPatIds)
import SimpFunBind(simpAllFunBind)
import SimpFieldLabels(simpFieldLabels)
import PFE_Rewrite
import PFE_StdNames
import MUtils

pbRewrite = Rewrite "pb" (remPats # getPrelValue "error")
lcRewrite = Rewrite "lc" (rmAllListComp # getPrelValue "concatMap")
pmRewrite = Rewrite "pm" $ do stdName <- getStdNames
			      ids <- getSimpPatIds (prelValue stdName)
			      return (simpAllPatMatch ids.simpAllFunBind)
fbRewrite = Rewrite "fb" (return simpAllFunBind)
flRewrite = Rewrite "fl" (simpFieldLabels # getPrelValue "error")
