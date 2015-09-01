module DrawLex where
import Monad(join)
import List(groupBy)
import Maybe(mapMaybe,fromMaybe)
import Fudgets
import FudDraw(ulineD')
import GIFAltFile
import OpTypes(eqBy)

import PfePlumbing(Label(..),lblPos,Icons,CertsStatus,addRefPos,refPos,assertionDefLbl)
import TokenTags as C
import HsLexerPass1(nextPos1,Pos(..))
import HsTokens as T
import HLexTagModuleNames
import RefsTypes(merge{-,T(..)-})
import PFE_Certs(CertName,certAttrsPath)
import CertServers(parseAttrs)
import HsName(ModuleName(..))
import TypedIds(NameSpace(..))

-- only the position is significant when locating a Label in a drawing
rootLabel = posLabel rootPos
  where rootPos = Pos (-1) (-1) (-1) -- not a valid file position
posLabel p = Lbl ((TheRest,(p,"")),Nothing)
origLabel orig = Lbl ((TheRest,(refPos orig,"")),Just orig)

fakeLex = labelD rootLabel . vboxlD' 0 . map g . map (expand 1) . take 2500 . lines

drawLex dir icons m colorGctx rs cs na =
    if quickfix
    then
     labelD rootLabel . vboxlD' 0 . map g .
     lines . concatMap (snd.snd)
    else
     labelD rootLabel . vboxlD' 0 .
     map (hboxD' 0 . map tokenD . autoAnnot {-. groupSpace-}) .
     take 2500 . -- Show at most 2500 lines !!
    groupBy sameLine . concatMap split . merge (map addRefPos rs) .
    convModuleNames
  where
    -- split tokens that span several lines:
    split ((t,(Pos n y x,s)),r) =
	[Lbl ((t,(Pos n y' x,l)),r)|(y',l)<-zip [y..] (lines (expand x s))]

    sameLine = eqBy (line.lblPos)

    tokenD lbl@(Lbl((t,(p,s)),r)) = markD . labelD lbl . colorD t . g $ s
      where markD =
              case r of
		Just (_,_,defs) | length defs/=1 -> ulineD' "red"
		_ -> id

            colorD t =
	      case t of
		NestedComment ->
		  case isCertAnnot s of
		    Just cert -> const (drawCertIcon dir icons m cs cert)
		    _ -> fgD C.Comment
		Commentstart  -> fgD C.Comment
		T.Comment     -> fgD C.Comment
		LiterateComment -> fgD C.Comment
		Reservedid    -> fgD Reserved
		Reservedop    -> fgD Reserved
	        Special       -> fgD Reserved
	        Specialid     -> fgD Reserved
		Conid         -> con r
		Qconid        -> con r
		Varsym        -> fgD VarOp
		Qvarsym       -> fgD VarOp
		Consym        -> fgD ConOp
		Qconsym       -> fgD ConOp
		IntLit        -> fgD Lit
		FloatLit      -> fgD Lit
		StringLit     -> fgD Lit
		CharLit       -> fgD Lit
		_             -> id
    fgD = hardAttribD . colorGctx

    con = maybe id (fgD . rcolor)
    rcolor ((_,sp),_,_) = if sp==ValueNames then Con else TCon

    autoAnnot ts = ts++autoannots
      where
        autoannots = map (nestedComment dummyPos.certAnnot) certs
	certs = concatMap (fromMaybe [] . flip lookup na) as
        as = mapMaybe assertionDefLbl ts
        dummyPos = lblPos (last ts)

    certAnnot cert = "{-#cert:"++cert++"#-}"
    nestedComment p s = Lbl ((NestedComment,(p,s)),Nothing)

{-
    groupSpace [] = []
    groupSpace (lbl@(Lbl((t,(p,s)),r)):ts) =
	 if isWhite lbl
	 then case span isWhite ts of
		(ws,ts') -> Lbl((t,(p,s++concatMap str ws)),r):groupSpace ts'
	 else lbl:groupSpace ts
       where
         str (Lbl((_,(_,s)),_)) = s

         isWhite (Lbl((Whitespace,(p,s)),r)) = all isSpace s
         isWhite _ = False
-}

drawCertIcon :: FilePath -> Icons -> ModuleName -> CertsStatus -> CertName ->
	        Drawing lbl Gfx
drawCertIcon dir (sad,icons) m cstatus cert =
    g (fileGfxAlt certIcon (certAttrsPath m cert dir) sad)
  where
    certIcon s =
     case (`lookup` icons) =<< lookup "type" (parseAttrs s) of
       Just cicons -> Right (cstatusIcon cicons (join (lookup cert cstatus)))
       _ -> Left "bad cert/unknown cert type"

certIcon (sad,icons) (cert,(Just attrs,cstatus)) =
  case (`lookup` icons) =<< lookup "type" attrs of
    Just icons -> cstatusIcon icons cstatus
    _ -> sad
certIcon (sad,_) _ = sad

cstatusIcon (valid,invalid,unknown) cstatus =
  case cstatus of
    Just (isvalid,_) -> if isvalid then valid else invalid
    _ -> unknown

-- isCertAnnot :: Monad m => String -> m CertName
isCertAnnot s =
  do '{':'-':'#':'c':'e':'r':'t':':':r <- return s
     '}':'-':'#':f <- return (reverse r)
     return (reverse f)

{- Why use "case" when you can use "do"? :-)
isCertAnnot s =
  case s of
    '{':'-':'#':'c':'e':'r':'t':':':r ->
        case reverse r of
          '}':'-':'#':f -> Just (reverse f)
          _ -> Nothing
    _ -> Nothing
-}

expand x "" = ""
expand x (c:s) =
    case c of
      '\t' -> replicate (x'-x) ' '++expand x' s
      _ -> c:expand x' s
  where Pos _ _ x' = nextPos1 (Pos 0 1 x) c

quickfix = argFlag "quickfix" False
