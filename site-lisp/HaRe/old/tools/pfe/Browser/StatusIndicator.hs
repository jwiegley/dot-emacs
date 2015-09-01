module StatusIndicator where
import Fudgets

data Status = Unknown | InProgress | InError | Good deriving (Eq,Ord)

statusF :: (Eq a,Enum a,Bounded a) => F (a,Status) b
statusF =
    nullF >==< 
    (createDrawStatus $ \ draw ->
     let u = draw Unknown
         pm = setBgColor bgColor . setInitDisp u . setBorderWidth 0
              . setMargin 0
     in placerF (horizontalP' 0) $
        listF [(l,displayF' pm>=^<draw)|l<-[minBound..maxBound]])

createDrawStatus cont =
    fg ["black"] $ \ black ->
    fg ["red","#ff3300","#ff0033","#cc0000","grey40","black"] $ \ red ->
    fg ["yellow","#ffff33","white"] $ \ yellow ->
    fg ["green3","#00cc00","#00c000","green","black"] $ \ green ->
    --fg ["blue3","#0000cc","#0000c0","blue","black"] $ \ blue ->
    let drawStatus status =
          g $ FixCD 12 $
	  case status of
	    Unknown     -> [noLight]
	    InProgress  -> yellowLight
	    InError     -> redLight
	    Good        -> greenLight

	redLight = colLight red
	greenLight = colLight green
	yellowLight = colLight yellow
	colLight fg = [light fg,noLight]
	light fg = (fg,[FillArc (Rect 2 9) 0 (64*360)])
	noLight = (black,[DrawArc (Rect 2 9) 0 (64*360)])
    in cont drawStatus
  where
    fg colspec cont =
      wCreateGCtx rootGCtx (gcFgA colspec) $ cont . gctx2gc


--instance Graphic Status where measureGraphicK = measureGraphicK . drawStatus
