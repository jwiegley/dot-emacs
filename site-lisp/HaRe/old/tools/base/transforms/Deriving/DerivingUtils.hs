module DerivingUtils(
    TypeInfo(..),DefTy(..),ConInfo(..),HsIdentI(..),IdTy(..),
    idTy,idName,
    fun,alt1,alt2,fun0,alt1',alt2',
    vars,app,apps,opapp,con,var,ident,wild,(-::),str,pair,
    hsLet,hsPApp,hsTyId,hsLit,hsPLit,HsLiteral(..),hsListComp,HsStmt(..),
    oneDef,toDefs,noDef,localVal,
    getBaseName,convCon,ModuleName(..),srcLoc,fakePos,
    isEnum,
    conj,
    --eq,bool,false,
    stdvalue,stdtype,stdclass,
    ( # ),
    module ModNames
  ) where
import TiNames as TI(conName,localVal,idName)
import TiClasses(var,con,ident,app,tuple,noDef,oneDef,toDefs)
import HasBaseStruct(hsInfixApp,hsPWildCard,hsFunBind,hsExpTypeSig,hsLit,
		     hsListComp,hsPLit,hsTyId,hsPApp,hsLet)
import HasBaseName(getBaseName)
import BaseSyntax
import TypedIds
import HsConstants as ModNames(mod_Prelude,mod_Ix)
import UniqueNames(origModule)
import SrcLoc1
import TiPNT()
import TiHsName()
import MUtils

default(Int)

vars x = [var (localVal (x++show n))|n<-[1..]]
apps args = foldl1 app args
pair x y = tuple [x,y]

opapp op e1 e2 = hsInfixApp e1 op e2
wild=hsPWildCard

fun = hsFunBind
alt2' src f p1 p2 e = HsMatch src f [p1,p2] (HsBody e) 
alt1' src f p e = HsMatch src f [p] (HsBody e) 

alt2 src f p1 p2 e = alt2' src f p1 p2 e noDef
alt1 src f p e = alt1' src f p e noDef

fun0 src f e = fun src [HsMatch src f [] (HsBody e) noDef]

isEnum = all isNullary
  where isNullary c = conArity c==0

convCon (t,ty) c0 = TI.conName (origModule c0) (getBaseName c0) t ty

e-::t = hsExpTypeSig loc0 e [] t
str s = hsLit s . HsString 
{-
andand = pv "&&"

bool = prelType "Bool"
false = prelCon "False" bool boolInfo
true = prelCon "True" bool boolInfo
boolInfo = TypeInfo {defType=Just Data,
		     fields=[],
		     constructors=[bc "False",bc "True"]}
  where
    bc c = ConInfo (prelCon c bool boolInfo) 0 Nothing
-}
conj andand true [] = ident true
conj andand true tsts = foldr1 (opapp andand) tsts

fakePos :: SrcLoc -> Int -> SrcLoc
fakePos (SrcLoc path char line col) n =
    SrcLoc (path++":derived_"++show col) char line n

stdvalue stdnames m n = stdnames ValueNames (m,n)
stdtype stdnames m n = stdnames ClassOrTypeNames (m,n)
stdclass = stdtype
