module SimpFunBind where
import Data.Maybe(isJust)
import HasBaseStruct
--import BaseSyntaxStruct(EI,PI,DI)
import SrcLoc1(HasSrcLoc,srcLoc)
import HsDeclStruct
import HsGuardsStruct
import TiNames(ValueId,localVal')
import TiClasses(HasDef,noDef)
import HsPatUtil(isPVar)
import MapDeclM(MapDeclM,mapDecls)

simpAllFunBind m = map simpFunBind m

{-+
Simplify function bindings to move patterns from the lhs of the definition into
a case expression in the rhs. This is similar to the translation described
in section 4.4.3.1 of the (revised) Haskell 98 report, except that we don't
produce a pattern binding with lambdas in the rhs, but a simple function
binding with variables on the lhs, to preserve type correctness.
(You have to avoid the annoying monomorphism restriction!)
-}
{-
simpFunBind ::
 (ValueId i,HasSrcLoc i,
  HasBaseStruct e (EI i e p [d] t c),
  HasBaseStruct p (PI i p), GetBaseStruct p (PI i p),
  HasDef [d] d,MapDeclM d [d],
  HasBaseStruct d (DI i e p [d] t c tp), GetBaseStruct d (DI i e p [d] t c tp))
  => d -> d
-}
simpFunBind d0 =
  case basestruct d of
    Just (HsFunBind s1 ms@(HsMatch s2 f ps rhs ds:ms')) | not trivial ->
         hsFunBind s1 [HsMatch s2 f (map hsPVar xs) (HsBody body) noDef]
       where
         --s2 = srcLoc f -- a more accurate position with the current parser
         trivial = null ms' && all (isJust.isPVar) ps
	 xs = [localVal' ("fx"++show n) (Just s2)|n<-[1..length ps]]
	 body = hsCase (hsTuple' (map hsEVar xs)) (map match2alt ms)
    _ -> d
  where d = mapDecls simpFunBind d0

match2alt (HsMatch s f ps rhs ds) = HsAlt s (hsPTuple' s ps) rhs ds

-- There are no tuples of arity 1, so...
hsTuple' [e] = e
hsTuple' es = hsTuple es
hsPTuple' s [e] = e
hsPTuple' s es = hsPTuple s es
