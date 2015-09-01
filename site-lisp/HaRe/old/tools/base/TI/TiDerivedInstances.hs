module TiDerivedInstances(derivedInstances) where
import HasBaseStruct
import HsDecl
import TI
import TiSolve(expandSynonyms)
import TiContextReduction(contextReduction'')
import TiInstanceDB(addInstKind)
import TiSCC(sccD)
import SrcLoc1

import Deriving(derive)
import FreeNamesBase()

import Data.Maybe(mapMaybe)
import Data.List(nub,partition)
import MUtils
import PrettyPrint

--import IOExts(trace) -- debugging

-- Figuring out what the derived instances are, without generating the
-- derived code.

derivedInstances ks stdnames modmap env ds =
     reduceInsts .
     map inst0 .
     concatMap (collectByFst.concatMap drv.mapMaybe basestruct) .
     sccD . filter isBaseTypeDec $ ds
  where
    inst0 (cn,is) = [(n,((c t,map c ts),(s,code t)))|(n,(t,ts))<-is]
      where c=app cn
	    s=srcLoc cn
	    code t=derive stdnames cn (definedTypeName t)
    drv d =
	case d of
	  HsNewTypeDecl s ctx t c  cls -> drv' cls t [c]
	  HsDataDecl    s ctx t cs cls -> drv' cls t cs
	  HsTypeDecl    {}             -> []
      where
	drv' cls t cons =
            [(cl,(derivedInstName' modmap cl tn,(t,syn (conArgTypes=<<cons))))
             |cl<-cls]
	  where tn=definedTypeName t

	conArgTypes con =
	  case con of
	    HsConDecl s _ _ c bangts -> map unbang bangts -- !!!
	    HsRecDecl s _ _ c fields -> map (unbang.snd) fields -- !!!

    app c t = hsTyCon c `hsTyApp` t
    syn = tmap (expandSynonyms env)

    isBaseTypeDec = maybe False isTypeDec . basestruct
    isTypeDec d =
	case d of
	  HsNewTypeDecl {} -> True
	  HsDataDecl    {} -> True
	  HsTypeDecl    {} -> True
	  _ -> False

     -- TODO: need fixed point interation for mutually recursive types!!
    reduceInsts [] = return []
    reduceInsts ([i]:is) =
      do i' <- reduce1 i
	 is' <- extendIEnv' [(fst i')] $ reduceInsts is
	 return (i':is')
    reduceInsts (is1:is) =
      do is1' <- mapM declare =<< instContext (instContext0 is1)
	 is' <- extendIEnv' (map fst is1') $ reduceInsts is
	 return (is1'++is')

{- old:
    reduceInsts (is1:is) =
      if all (null.freeTyvars.fst.fst.snd) is1
      then reduceInsts ([[i]|i<-is1]++is)
      else
      fail.pp$
        sep [ppi "Deriving for mutually recursive types with parameters not implemented yet:",
	     nest 4 $ ppiFSeq (map (fst.fst.snd) is1)]
-}
    reduce1 (n,((p,ps),(s,mcode))) =
      do _:>:ps' <- extendIEnv' [(p,(n,[]))] $ simplify s ps
	 --trace (pp (ps$$ps')) $ do
	 declare ((p,(n,ps')),(ps,(s,mcode)))

    declare (i@(p,(n,ps')),(_,(s,mcode))) =
      do methods <- posContext s mcode
	 let d = hsInstDecl s (Just n) ps' p (toDefs methods)
	 return (i,d)

    simplify s ps =
      do ns <- map (flip dictName' (Just s)) # freshlist (length ps)
         unzipTyped # contextReduction'' (zipTyped (ns:>:ps))

   --In progress: fix point iteration for mutually recursive types:
    instContext is =
       do is' <- mapM (instContext1 (map fst is)) is
	  if and (zipWith eqinst is is')
            then return is
	    else instContext is'

    instContext1 is (i@(p,(n,ctx)),j@(ps,(s,c))) =
       do _:>:ctx' <- extendIEnv' is $ simplify s ps
	  return ((p,(n,ctx')),j)

    instContext0 is = [((p,(n,[])),(ps,c))|(n,((p,ps),c))<-is]

    extendIEnv' = extendIEnv . map (addInstKind ks)

    {-+
    If there was an Ord instance for predicates, we could just nub and sort
    and compare for equality. Since we only have Eq, it's a bit more clumpsy...
    -}
    eqinst i1 i2 = eqctx (ctx i1) (ctx i2)
      where
        ctx ((_,(_,c)),_) = nub c
	
	eqctx [] ps2 = null ps2
	eqctx (p1:ps1) ps2 =
          case partition (==p1) ps2 of
            ([p2],ps2') -> eqctx ps1 ps2'
	    _ -> False
