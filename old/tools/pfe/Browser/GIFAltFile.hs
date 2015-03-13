-- This file belongs in Fudgets/Internet/Lib/images...
module GIFAltFile where
import AllFudgets
import GIFparser
import GIFdecompress
import ImageGraphics
import DialogueIO

gifFileAlt = fileGfxAlt parseGifImage

parseGifImage s =
  case parseGIF s of
    Right gif -> Right (GIFImage Nothing (decompressGIF gif))
    Left msg -> Left msg

data FileGfxAlt altgfx gfx
  = FileGfxAlt (String->Either String gfx)
               FilePath
	       (DialogueIO.IOError->altgfx)

fileGfxAlt parse path alt = FileGfxAlt parse path (const alt)
fileGfx parse path = FileGfxAlt parse path (error.show)

instance (Graphic altgfx,Graphic gfx) => Graphic (FileGfxAlt altgfx gfx) where
  measureGraphicK (FileGfxAlt parse path alt) gctx k =
      hIOerr (ReadFile path) err $ \ (Str s) ->
      case parse s of
	Left msg -> err (OtherError msg)
	Right gfx -> measureGraphicK gfx gctx k
    where
      err e = measureGraphicK (alt e) gctx k
