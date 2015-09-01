module HistoryButtonsF where
import AllFudgets hiding (StreamProcIO(..))
import ReactiveF
import Monad(when)

-- Mostly taken from WWWBrowser...

historyButtonsF = loopThroughRightF ctrlF buttonsF
  where
    ctrlF = getFirst $ reactiveF ctrl . state0
    state0 first = ([],first,[])

    getFirst cont = getF $ either (\ _ -> getFirst cont) $
			   either cont (\ _ -> getFirst cont)

    ctrl = either fromButtons fromOutside
    fromButtons = either fromBack fromForward

    output = put . Right
    changeback = put . Left . Left
    changeforward = put . Left . Right

    set' (bs,cur,fs) =
       do set (bs,cur,fs)
	  changeback bs
	  changeforward fs

    goForward 0 h = return h
    goForward n (_,_,[]) = rfail
    goForward n (bs,cur,f:fs) = goForward (n-1) (cur:bs,f,fs)

    goBack n h = fliph `fmap` goForward n (fliph h)
    fliph (bs,cur,fs) = (fs,cur,bs)

    fromBack n = setput =<< goBack n =<< get
    fromForward n = setput =<< goForward n =<< get
    setput h@(_,cur,_) = set' h >> output cur

    fromOutside (Left new) =
        do (bs,cur,fs) <- get
	   when (cur==new) rfail
	   set' (cur:bs,new,[])

    fromOutside (Right new) =
        do (bs,cur,fs) <- get
	   set' (bs,new,fs)

    buttonsF = mbuttonF kl lArrowD >+< mbuttonF kr rArrowD
      where
         kl = k "Left"; kr = k "Right";
         k sym = setKeys [([Mod1],sym)]::Customiser (ButtonF a)

    mbuttonF keys lblf =
        post >^=< popupMenuF [] (dbuttonF keys lblf) >=^^< concatMapSP pre
      where
        pre alts = [Left (zip [1..limit] alts),Right (null alts)]
	limit = 30 -- maximum number of menu entries
	post = either id (const 1)

    dbuttonF keys lblf =
       buttonF'' keys (lblf True) >=^< Left . setLabel . lblf >=^^< idempotSP

    lArrowD = arrowD pts r
      where
	r = rR 12 3 4 4

    rArrowD = arrowD pts' r
      where
	pts' = [pP 16 10 - p | p<-pts]
	r = rR 0 3 4 4

    arrowD pts r disabled =
	spacedD (hvMarginS m m) $
	if disabled then outlineD else stackD [fillD,outlineD]
      where
        fillD =
	  fgD "white" $ fd [FillPolygon Convex CoordModeOrigin pts,
			     FillArc r 0 (64*360)]
        outlineD =
	  fgD ["blue4","#0000cc","black"] $
	      fd [DrawLines CoordModeOrigin pts,DrawArc r 0 (64*360)]

	m = Point 1 2
	fd = g . FixD (Point 17 11)

    pts = [pP 0 5,pP 5 0,pP 5 3,pP 10 3,pP 10 7,pP 5 7,pP 5 10,pP 0 5]
