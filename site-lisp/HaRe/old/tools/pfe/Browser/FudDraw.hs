module FudDraw(module F,module FudDraw) where
import AllFudgets as F(
  Point(..),g,hFiller,
  fgD,blankD,vboxlD',hboxD,placedD,spacedD,boxD,labelD,stackD,
  paragraphP',ifSizeP,verticalP',spacersP,horizontalAlignP',
  idS,hMarginS,centerS,bottomS)

ulinkD s = fgD "blue" $
           spacedD centerS $
           stackD [spacedD bottomS (g (hFiller 1)),s]

ulineD' color s = spacedD centerS $
                  stackD [fgD color $ spacedD bottomS (g (hFiller 1)),s]

hboxcaD = hboxcaD' sep
hboxcaD' sep = placedD (horizontalAlignP' sep) . boxD

wideOrTallD sep nds = placedD (wideOrTallP sep ns) (boxD ds)
  where (ns,ds) = unzip nds

wideOrTallP sep ns = ifSizeP cmp wideP (tallP ns)
  where
    wideP = horizontalAlignP' sep
    tallP ns = verticalP' 0 `spacersP` map indentS ns

    cmp (Point w1 _) (Point w2 _) =
      w1<=maxwidth || w1-w2<150 && w2>9*w1 `div` 10


--indentD n = fgD "grey85" (filledRectD (pP (sep*n) 5))
indentD (0,d) = d
indentD (n,d) = spacedD (indentS n) d

indentS 0 = idS
indentS n = hMarginS (sep*n) 0


sep = 6 -- show be determined from the font
maxwidth = 500
