module IdInfo where
import PrettyPrint(pp)
--import HsIdent(getHSName)
--import HsModule(ModuleName(..))
import HsTokens
import PfePlumbing(refPos)
import UniqueNames(optOrigModule)
import QualNames(getQualified)
import HasBaseName(getBaseName)
--import RefsTypes
--import PFE0(ModuleFixities)
--import FudgetIOMonad1(SrcToken)
--import ParsedSyntax(Id)

import Maybe(fromMaybe)
import MUtils(( # ),mapFst)

--idInfo :: Refs -> ModuleFixities Id -> SrcToken -> [String]
idInfo refs infixes ((t,(p,s)),optref) =
    case optref of
      Just ((r,_),_,defs) {- | s'==s -} ->
	  (occurences,def,showDefs defs ++ infixinfo)
	where
          showDefs [] = [s++": "++"not in scope??"]
	  showDefs defs = map showDef defs

	  def = case defs of
		  [o] -> Just o
		  _ -> Nothing
	  occurences =
	    maybe [] (\o->[refPos r|r@(_,_,[o'])<-refs,o'==o]) def

          showDef (o,t') = {-show r++" "++-}s++": "++shO o++", "++pp t'
          {-
	  orig (Co t) = ", constructor of "++t
	  orig (Fi t) = ", field of "++t
	  orig (Me t) = ", method of "++t
	  orig V = ""
	  orig T = ", a type"
	  orig Cl = ", a class"
	  -}

	  infixinfo =
	    case defs of
	      [(qn,_)] ->
		fromMaybe [""] $
		do m <- optOrigModule qn
		   is <- mapFst getBaseName # lookup m infixes
		   fixity <- lookup (getBaseName.getQualified$ qn) is
		   return [pp fixity]
	      _ -> [""]

      --Just (s',r,_,defs) -> ([],Nothing,["?? "++s'++" /= "++s])
      _ -> ([],Nothing,
	       if t==TheRest
	       then []
	       else [show t++" at "++show p])
  where
    shO n = case optOrigModule n of
	      Just m -> pp m++"."++pp (getQualified n)
	      _ -> pp n++" (local)" -- improve!!
    --shO = either shQ shL
    --shQ (m,n)=m++"."++n
    --shL (path,p) = "local at "++show p
