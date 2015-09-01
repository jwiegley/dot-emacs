module HsDeclUtil where

import HsDeclStruct
import HsDeclMaps
--import MUtils
--import HsGuardsMaps
import SrcLoc1
import SrcLocPretty
import PrettyPrint(pp)

-- Finds all of the free variables in a D structure.

freeVarsD fvd fve d = 
    accD (++) (++) (++) (++) (++) (++) 
         (mapDI id fve (const [])
	           (concatMap fvd)
	           (const [])
	           (const [])
	           (const [])
	  d)
	 []


-- Rewrite expressions inside declarations given fixity information.

rewriteD rwe env d = mapDI id (rwe env) id id id id id d

-- New version: rewrite expressions and patterns,
-- and also recurse into nested declarations.
rewriteAllD rwe rwp rwds = mapDI id rwe rwp rwds id id id

fixitiesD ds =[(n,fixity) | HsInfixDecl _ fixity ns<-ds, n<-ns]


instance HasSrcLoc (DI i e p ds t c tp) where
  srcLoc d =
    case d of
      HsTypeDecl s tps t                 -> s
      HsNewTypeDecl s cntxt tps cd names -> s
      HsDataDecl s cntxt tps cds names   -> s
      HsClassDecl s c tp fd ds           -> s
      HsInstDecl s optn c tp ds          -> s
      HsDefaultDecl s t                  -> s
      HsTypeSig s nms c tp               -> s
      HsFunBind s matches                -> s
      HsPatBind s p rhs ds               -> s
      HsInfixDecl s fixity names         -> s

      HsPrimitiveBind s nm t             -> s
      HsPrimitiveTypeDecl s cntxt nm     -> s


instance HasSrcLoc (HsMatchI i e p ds) where
    srcLoc (HsMatch s _ _ _ _) = s

unbang bt = accBangType const bt ()

conargcnt con =
  case con of
    HsConDecl s _ _ c args -> length args
    HsRecDecl s _ _ c fields -> sum (map (length.fst) fields)

conctx con =
  case con of
    HsConDecl s _ ctx c args -> ctx
    HsRecDecl s _ ctx c fields -> ctx

instance HasSrcLoc (HsConDeclI i t c) where
  srcLoc con =
    case con of
      HsConDecl s _ _ c argrs -> s
      HsRecDecl s _ _ c fields -> s

chkNewtype con =
  if conargcnt con==1
  then if null (conctx con)
       then return ()
       else fail $ pp (srcLoc con)++
                   ": existential newtype constructors can't have a context"
  else fail $ pp (srcLoc con)++
	      ": a newtype constructor must have exactly one argument"
