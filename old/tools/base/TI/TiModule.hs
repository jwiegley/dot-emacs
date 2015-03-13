{-+
This module defined the function #tcModule#, which type checks a single
module, the function #tcModuleGroup#, which type checks a group
of mutually recursive modules.
-}
module TiModule(tcModule,tcModuleGroup,representative,joinModules,
                monomorphismRestriction) where
import Data.Maybe(mapMaybe,fromJust)
import Data.List(sort)

import TiDefault(resolveToplevelAmbiguities)
import TI
--import TiPrelude(pt)
import SrcLoc1(srcFile)
import HasBaseName(getBaseName)

import HsModule
import HasBaseStruct
import HsDeclStruct

import MUtils

{-+
Type checking a single module
-}
tcModule stdNames mod =
  tcModule' stdNames id (const (getBaseName (hsModName mod))) mod

tcModule' stdNames rewrite modmap (HsModule s m es imps ds) =
  withStdNames stdNames $
  do integer <- prelTy "Integer"
     double <- prelTy "Double"
     let defaultDefaults = [integer,double]
	 dss = if null dss0 then [defaultDefaults] else dss0
	   where dss0 = defaultDecls ds
     emap (HsModule s m es imps) #
       (inModule modmap dss $ checkModule2 $ tcTopDecls rewrite ds)
  where
    -- These functions are present only beause they are needed to implement
    -- the annoying monomorphism restriction...
{-
    -- Without defaulting:
    checkModule1 mM =
      do (m:>:(insts,(ks,ts)),(dicts,kpreds,s1)) <- getSubst mM
         extendkts ks $ extendts ts $ extendIEnv insts $
	  do catchAmbiguity dicts
	     let s = apply s1
	     s m>:(insts,(ks,s ts))
-}
    -- With defaulting:
    checkModule2 mM =
      do (m:>:(insts,(ks,ts)),(dicts,kpreds,s1)) <- getSubst mM
         extendkts ks $ extendts ts $ extendIEnv insts $
          do --catchAmbiguity dicts
	     (s2,r) <- resolveToplevelAmbiguities dicts
	     let s = apply s2 . apply s1
	     r (s m)>:(insts,(ks,s ts))

defaultDecls ds = [ts|HsDefaultDecl s ts<-mapMaybe basestruct ds]

{-+
Type check a mutually recursive group of modules by joining them
into one module...
-}
tcModuleGroup stdNames rewrite ms =
    emap (splitModule ms) #
      tcModule' stdNames rewrite (moduleNameMap ms) (joinModules ms)
  where

    splitModule ms HsModule{hsModDecls=ds} = map collectDecls ms
      where
         collectDecls (HsModule s m i e _) =
	     HsModule s m i e (filterDefs sameFile ds)
	   where
	     f = srcFile s
	     sameFile d = srcFile d==f

moduleNameMap ms path =
  fromJust . lookup path $ [(srcFile m,getBaseName (hsModName m))|m<-ms]

joinModules mods@(_:_) =
    fakeModule $ unzip3 [(s,m,ds)|HsModule s m _ _ ds<-mods]
  where
    fakeModule (s:_, ms, dss) =
        HsModule s (representative ms) Nothing [] (concatDefs dss)
joinModules [] = error "Bug: TiModule.joinModules []"

representative = head . sort -- pick one representative from the scc
