{-+
Some source transformations need to refer to entities defined in the Prelude
or other standard library modules.
-}
module PFE_StdNames where
import Data.List(intersect)

import TypedIds(NameSpace(..),namespace)
import HsConstants(mod_Prelude,mod_Ix)
import PFE0(allModules)
import PFE2(getExports)
import TiNames(topName)
import ScopeModule(origName)
import HasBaseName(getBaseName)
import HsIdent(HsIdentI(..))
import SourceNames(fakeSN)
import Relations(applyRel)
import WorkModule(Ent(..))

import PrettyPrint(pp,(<+>),(<>))
import MUtils(( # ))

stdValue stdName m n = stdName ValueNames (m,n)
prelValue stdName = stdValue stdName mod_Prelude

getPrelValue n = getStdValue mod_Prelude n

getStdValue m n =
  do stdName <- getStdNames
     stdValue stdName m n

getStdNames =
  --pfe4 $
  do allms <- allModules
     stdNames . prune # getExports (Just (stdms `intersect` allms))
  where
    prune = filter ((`elem` stdms).fst)
    stdms = [mod_Prelude,mod_Ix]

    stdNames es ns (m,n) = maybe merr (find n . snd) (lookup m es)
       where
         merr = fail $ pp $ "Standard library module not avaialble:"<+>m
	 find n exprel =
           case filter ((==ns).namespace) $ applyRel exprel (fakeSN n) of
	     [e] -> return (ent2pnt e)
	     [] -> fail $ pp $ "Standard entity not avaialble:"<+>m<>"."<>n
	     _ ->  fail $ pp $ "Standard entity is ambiguous:"<+>m<>"."<>n

    ent2pnt (Ent m (HsCon i) t) = HsCon (topName Nothing m (bn i) (origt m t))
    ent2pnt (Ent m (HsVar i) t) = HsVar (topName Nothing m (bn i) (origt m t))
    bn i = getBaseName i
    origt m = fmap (osub m) 
    osub m n = origName n m n
