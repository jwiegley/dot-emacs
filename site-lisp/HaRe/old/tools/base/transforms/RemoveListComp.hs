module RemoveListComp where
import Substitute
import Recursive
import HasBaseStruct
import BaseSyntax
import SrcLoc1
import HsConstants(mod_PreludeList)
import DerivingUtils(alt1,oneDef)
import TiNames(ValueId,localVal',topVal)
import TiClasses(HasDef)

rmAllListComp cm m = mapExp (rmListComp cm) m

class RmListComp i s | s->i where
  rmListComp :: HsIdentI i -> s -> s

instance RmListComp i s => RmListComp i [s] where rmListComp = map . rmListComp

rmListCompE concatMap e = rmListCompE' r concatMap e

rmListCompE' r cm e0 =
    case mapEI id (rmListComp cm) id (rmAllListComp cm) id id e0 of
      HsListComp stmt -> compileListComp cm stmt
      e -> r e

{-+
Translation of list comprehensions, as described in section 3.11
of the Haskell 98 report
-}
{-
compileListComp ::
   (ValueId i,
    HasBaseStruct e (EI i e p ds t c),
    HasBaseStruct p (PI i p),
    HasBaseStruct d (DI i e p ds t c tp),
    HasDef ds d)
  => HsStmt e p ds -> e
-}
compileListComp concatMap = comp
  where 
    comp stmt =
      case stmt of
	HsGenerator s p e stmt ->
	     hsLet okDef (hsId concatMap `hsApp` hsEVar ok `hsApp` e)
	   where
	     ok = localVal' "ok" (Just s) -- should be a fresh variable
	     okDef = oneDef (hsFunBind loc0 okEqns)
	     okEqns = [okM p (comp stmt),
		       okM hsPWildCard (hsList [])]
	     okM = alt1 loc0 ok

	HsQualifier e stmt -> hsIf e (comp stmt) (hsList []) 
	HsLetStmt ds stmt -> hsLet ds (comp stmt)
	HsLast e -> hsList [e]
