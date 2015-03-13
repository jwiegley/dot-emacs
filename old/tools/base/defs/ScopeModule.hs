{-+
This module provides the function #scopeModule# which takes abstract
syntax trees returned by the parser, where idientifers are annotated with
the position they occurred at in the source file, and produces abstract
syntax trees where the identifiers are annotated with the following
extra information:

  * Tagging to make every identifier globally unique, i.e., you can tell
    which entity (binding occurence) an identifier refers to, without knowing
    which scope it occurs in.
    Top-level entities are identified by their original names (M.n).
    Local entities are idenfified by their names in combination
     with a source position.

  * Tagging to tell what kind of entity the identifiers refer to (a value,
    a type class, a data constructor, ...)

The type #PNT# is the type used for identifiers holding this extra tagging
information.

(The function #numberNames# is responsible for
making names unique. It currently uses source positions, but it could
generate unique numbers instead, in which case the parser wouldn't have to
provide any position information.)
-}
module ScopeModule(scopeModule,XRefInfo,checkRefs,origName) where

import HsModule(hsModName)
import HsIdent(HsIdentI(..),getHSName,mapHsIdent)
import HsName(HsName,ModuleName)
import SrcLoc1(SrcLoc,srcLoc)
import HasBaseName

import WorkModule(inscpList) --WorkModuleI,ExpRel,inScope,
import Relations(relToList)
import TypedIds--(IdTy(..),blankTypeInfo,namespace,belongsTo)
import NameMaps
import NumberNames(numberNames,PN(..),Orig(G),orig,origModule,eqSrc,optLoc,unique)
import PNT
import ScopeNames
import UniqueNames(optOrigModule)
--import SourceNames(srcName,SN)

import QualNames(getQualified,mkUnqual,mkQual)
import Ents(Ent(..))

import PrettyPrint

import OutputM
import EnvM
import Data.List(partition,nub)
import Data.Maybe(fromJust)
import MUtils(mapSnd)
import OpTypes(ordBy)
import FiniteMap1

--import IOExts(trace) -- for debugging

{-
scopeModule :: ... => ...
                   -> HsModuleI i (ds (SN HsName))
                   -> (HsModuleI i (ds PNT),[XRefInfo])
-}
scopeModule (wm,exports) mod
    = mergeOutputM -- merge now to avoid having to sort later
    . seqNames
    . mapNames2 TopLevel (pickScope m envs HsVar, pickScope m envs HsCon)
    . addScope modenv
    . numberNames $ mod
  where
    m = getBaseName (hsModName mod)
    modenv = topenv wm
    envs = (modenv,mapSnd (impenv.relToList) exports)

    mergeOutputM = foldOutput [] (:[]) merge'

    merge' xs [] = xs
    merge' [] ys = ys
    merge' xxs@(x:xs) yys@(y:ys) = if ordBy srcLoc' x y
				   then x:merge' xs yys
				   else y:merge' xxs ys

    srcLoc' (_,i,_) = srcLoc i

checkRefs :: [XRefInfo] -> [(SrcLoc,Doc)]
checkRefs = concatMap checkRef
  where
    -- Exports and imports have already been checked by the module system code,
    -- so no need to check again. TODO: import specs are checked agains the
    -- environment...
    checkRef ((ExpEnt {},_),x,os) = []
    checkRef ((ImpEnt {},_),x,os) = []
    checkRef ((role,sp),x,os) =
      case os of
	[_] -> []
        [] -> [(srcLoc x,"not in scope:"<+>x)]
	_ -> [(srcLoc x,"ambiguous:"<+>x<+>ppiFTuple (map origname os))]
    origname (x,_) = origModule x<>"."<>getQualified x

--type Filter x y = FiniteMap x y->[y]

type SPName = (PName,ScopeFM)
type Scope = [(PIdent,IdTy PId)]
type ScopeFM = FiniteMap (HsIdentI HsName) Scope
type ImportScope = [(ModuleName,ScopeFM)]
type XRefInfo = ((Role (),NameSpace),PIdent,Scope)

pickScope :: ModuleName ->
             (ScopeFM,ImportScope) ->
             (PName->PIdent)->
	     Occurence SPName ->
	     SPName ->
	     OutputM XRefInfo PNT
pickScope m (modenv,ex) c (dctx,sp) (i,scope) =
     checkref . partition (isLocal.getHSName.fst) . nub . filterSame $ scope'
  where
    scope' = case dctx of
	       ImpEnt m _ -> fromJust (lookup m ex)
	       _ -> scope

    filterSame =
      case dctx of
	{- This should implement the revised Haskell 98 scoping rules for
	   instance declarations and subordinate names in imports/exports.-}
	Def (Instance (cl,_)) -> filterSameSub cl
	ExpEnt (Just (i,_))   -> filterSameSub i
	ImpEnt m (Just (i,_)) -> filterSameSub i
	FieldLabel            -> filter isField . filterSameNormal
	Sig TopLevel	      -> filterSameModule
	Use                   -> filter notLogic . filterSameNormal
	_                     -> filterSameNormal

    filterSameNormal env =
       -- i' `eqSrc` c i && sp == namespace ity'
       [it|it@(i',ity')<-lookenv env (c i),sp==pnamespace ity']

    notLogic (_,Assertion) = False
    notLogic (_,Property)  = False
    notLogic _             = True

    filterSameModule = filter sameModule . filterSameNormal
      where sameModule (i,_) = optOrigModule i == Just m

    -- P-Logic: conids can refer to properties&assertions in imports&exports
    pnamespace = if isExpOrImp then impexpnamespace else namespace
      where
        isExpOrImp =
          case dctx of
	    ExpEnt Nothing -> True
	    ImpEnt _ Nothing -> True
	    _ -> False
	impexpnamespace ity =
          case ity of
	    Assertion -> ClassOrTypeNames
	    Property -> ClassOrTypeNames
	    _ -> namespace ity

    filterSameSub i env = filtFM (sameSub env i) env
      where filtFM p = filter p . concat . eltsFM

    sameSub env iowner =
      case filter (isClassOrType.snd) $ lookenv env (HsCon iowner) of
	[(HsCon c,idty)] ->
	    case [orig s|s<-subs,s `eqSrc` n] of
	      [o] -> sameSub' o
	      [] -> --trace ("subordinate not found "++show (iowner,i,subs)) $
		    const False
	      _ -> --trace ("ambiguous subordinate name "++show (iowner,i,subs)) $
		   const False -- data/class with name duplications...
	  where
	    subs = subordinates idty
	    n = getQualified i -- i should be unqualified
	    sameSub' o (i,idty) = orig i==o && isSubordinate idty

	[] -> --trace ("not in scope "++show iowner) $
	      const False
	ents -> --trace ("ambiguous owner of subordinate names "++show (iowner,ents)) $
		const False

    isField (_,FieldOf {}) =  True
    isField _ = False

    isLocal (PN _ (G {})) = False
    isLocal _ = True -- hmm

    checkref (l:_,_) = ref [l] -- innermost binding, ambiguities not detected
    checkref (_,gs)  = ref (filterdefs gs)

    -- Defining occurences do not themselves conflict with imported names,
    -- except in instances, which aren't really defining occurences.
    filterdefs =
      case dctx of
	Def (Instance _) -> id
	Def _ -> filter ((==m).origModule.getHSName.fst)
	_ -> id

    ref is = output ((strip dctx,sp),c i,is) >>
	     case is of
	       [(oi,idty)] -> return (PNT (keepSrcName oi) idty (optLoc i))
	       _           -> return (PNT i (fakeidty sp) (optLoc i))
      where keepSrcName oi = PN (getBaseName i) (orig oi)

    -- To avoid recursive type:
    strip = fmap (const ())

    -- To avoid failing on references to ids not in scope
    fakeidty ValueNames = Value
    fakeidty ClassOrTypeNames = Type blankTypeInfo


addScope env m =
    --trace (show (hsModName m,wm)) $
    withEnv env (scopeNames extend m)
  where
    --global (ni,idty) = (N i (G i),idty)
    --  where N i _ = getHSName ni
    --local (ni,idty) = (getHSName ni,idty)

    extend new old = extenv old (filter notoldtyvar (mapSnd conv new))
      where
        --oldtyvars = [i|(HsVar i,Type {})<-old]
        notoldtyvar (i@(HsVar _),Type {}) = null [()|(_,Type{})<-lookenv old i]
        notoldtyvar _ = True

    conv = fmap getQualified

envMap = extenv emptyFM
extenv env bs = addListToFM_C (flip (++)) -- innermost binding first in the list
                              env
			      [(getBaseName i,[it])|it@(i,_)<-bs]
lookenv env i = lookupWithDefaultFM env [] (getBaseName i)

--topenv :: WorkModuleI HsName Id -> [(HsIdentI (PName),IdTy (PId))]
topenv wm = envMap [(origIdent qn m i,origt m t)|(qn,Ent m i t)<-inscpList wm]
      where
        origt m = fmap (osub m)
        osub m n = origName n m n
	    -- This generates references to names not necessarily in scope...

{-
impenv ::
  (Unique n, HasBaseName qn HsName, QualNames qn ModuleName n1,
   HasBaseName n ib) =>
  [(n1, Ent n)]
  -> FiniteMap (HsIdentI HsName) [(HsIdentI (PN HsName), IdTy (PN ib))]
--}
impenv exprel =
    envMap [(origIdent (unq m n) m i,origt m t)|(n,Ent m i t)<-exprel]
  where
    unq m n = mkUnqual n `asTypeOf` mkQual m n
                      -- ^ this eliminates an ambiguite that was accepted by GHC
    origt m = fmap (osub m)
    osub m n = origName n m n

origIdent qn m = mapHsIdent (origName qn m)
origName qn m n = PN (getBaseName qn) (unique m n)
--origName qn m n = PN (getBaseName qn) (G m (getBaseName n))

--instance (Printable a,Printable b) => PrintableOp (a,b) where
--  ppiOp (x,y) = "`("<>x<>","<>y<>")`"

subordinates (Class _ ms) = {-map HsVar-} ms
subordinates (Type TypeInfo {constructors=cs,fields=fs}) =
  {-map HsVar-} fs++map ({-HsCon .-} conName) cs
subordinates _ = []

