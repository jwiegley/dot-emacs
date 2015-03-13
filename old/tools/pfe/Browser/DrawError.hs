module DrawError(drawTypeError,drawScopeErrors) where
import FudDraw
import TiError
import DrawDoc
import PfePlumbing(InfoLbl(..),srcLocLbl)
import PrettyPrint(ppi)

drawScopeErrors = vboxlD' 0 . map drawScopeError
drawScopeError (loc,msg) = hboxcaD [drawSrcLoc loc,g ":",drawDoc msg]

drawTypeError m err =
  case err of
    InContext ctx err -> ctxD (drawContext m ctx) (drawTypeError m err)
    Other doc -> drawDoc doc

drawContext m ctx =
  case ctx of
    AtPos loc Nothing -> drawSrcLoc loc
    AtPos loc (Just d) -> hboxcaD [drawSrcLoc loc,drawDoc d]
    DeclCtx is -> hboxcaD (g "In the declaration of":map drawIdent is)
    ModuleCtx ms -> hboxcaD (msg:map (drawModule m) ms)
      where msg = if length ms==1 then g "In module" else g "In modules"
    OtherCtx d ls -> ctxD (drawDoc d) (vboxlD' 0 (map drawLoc ls))
      where
        drawLoc (d,loc) = ctxD (drawDoc d) (hboxcaD [g "from",drawSrcLoc loc])

drawIdent = drawLink DefLbl
drawSrcLoc = drawLink srcLocLbl

drawModule current m =
   if m==current then drawDoc (ppi m) else drawLink ModuleLbl m

drawLink lbl dst = labelD (lbl dst) (ulinkD (drawDoc (ppi dst)))

ctxD d1 d2 = vboxlD' 0 [d1,indentD (2,d2)]
